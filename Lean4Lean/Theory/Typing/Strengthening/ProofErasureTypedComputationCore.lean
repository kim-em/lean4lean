import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationPrimitives
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore

/-! # Concrete core computations as typed chains

Registered ordinary pattern traces and repaired quotient prefixes are already
forward computations. Their source assignment is preserved on every edge.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Retag a chain at any actual source assignment. Ordinary uniqueness aligns
each edge, while its erased computation remains identical. -/
theorem TypedComputationEq.at_source_type
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ a T)
    (H : TypedComputationEq D Γ a b A) : TypedComputationEq D Γ a b T := by
  induction H with
  | step HE R => exact .step ((show env.IsDefEqU univs Γ _ _ from ⟨_, HE⟩).of_l henv hΓ ht) R
  | symm H ih =>
    have ht' := ((show env.IsDefEqU univs Γ _ _ from ⟨_, H.defeq.symm⟩).of_l henv hΓ ht).hasType.2
    exact (ih ht').symm
  | trans _ _ ih₁ ih₂ =>
    have HL := ih₁ ht
    exact HL.trans (ih₂ HL.defeq.hasType.2)

/-- Concrete core paths embed at stage zero of the full union. -/
theorem iota_compute_static_structure (R : Compute (ErasedIotaPrimitive D) a b) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a b :=
  R.scoped (fun H => .base ⟨0, .inl (.inl H)⟩)

/-- An ordinary pattern trace has a context-independent core realization:
registration turns its supplied checks into checks from source typing. -/
theorem pattern_trace_compute
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (H : PatternReductionTrace env univs Pat Γ a b) : PureObservation.PatternCompute D a b := by
  induction H with
  | refl => exact .refl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | pattern hp hm hc =>
    exact .pattern hp hm (PureObservation.ConcretePattern.checkFromTyping henv (hcon hp) hc)
  | beta => exact .base (.base .beta)
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | lam _ ih => exact .lam .refl ih

/-- Every concrete pattern trace gives a typed chain from its source typing. -/
theorem TypedComputationEq.of_pattern_trace
    (hs : D.Sound env univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ a T)
    (H : PatternReductionTrace env univs Pat Γ a b) : TypedComputationEq D Γ a b T := by
  have R := pattern_trace_compute (D := D) hcon H
  exact .step (R.simAt hs hΓ T ht)
    (iota_compute_static_structure (proofErase_pattern_compute_forward hs hcon hΓ ht R))

/-- Proposition-source quotient prefixes compute in the total environment
collection, with no type-fork joining or native coverage premise. -/
theorem TypedComputationEq.quot_prefix
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (mkApps (.const ``Quot.lift levels) args) T)
    (H : QuotPrefixUnfold env univs Γ levels args rhs) :
    TypedComputationEq EnvironmentCore.definitions Γ
      (mkApps (.const ``Quot.lift levels) args) rhs T :=
  .step ((H.defeq henv hΓ).of_l henv hΓ ht)
    (iota_compute_static_structure (EnvironmentCore.quotient_prefix_forward hcon hΓ ht H))

end Lean4Lean.VEnv.Strengthening
