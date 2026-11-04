import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedCoreJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureQuotCoreConfluence

/-! # Ordinary core computation mixed with controlled beta expansion

Finite paths may interleave ordinary primitives, beta, constant expansion and
native identity expansion. Typed core confluence gives an exact core common
reduct, even when native guards use a larger relation. This admits arbitrary
source syntax and does not assume confluence of the expanded relation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Ordinary primitives and the two controlled beta expansions. Explicit
universe conversion and singleton/Eq-prefix roots are not included here. -/
def ErasedCoreExpansion (D : PureObservation.Definitions)
    (Recovery : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ErasedIotaPrimitive D a b ∨ ConstantExpansion a b ∨ NativeIdentityExpansion Recovery Δ a b

/-- Source-typed descent holds when the native guard relation descends. -/
theorem erased_core_expansion_descent (hs : D.Sound env univs)
    (hr : ErasedScopedPrimitiveDescent Recovery) :
    ErasedScopedPrimitiveDescent (ErasedCoreExpansion D Recovery) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  rcases R with R | R | R
  · exact ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs) hΓ hΓ' W ht R
  · exact erased_constantExpansion_descent hΓ hΓ' W ht R
  · exact erased_nativeIdentityExpansion_descent hr hΓ hΓ' W ht R

/-- Every mixed root is joined in the ordinary core. Expansion guards need no
transport because the selected wrapper beta-contracts to its source. -/
theorem erased_core_expansion_root_join
    (R : ErasedCoreExpansion D Recovery Δ a b) : ComputeJoin (ErasedIotaPrimitive D) a b := by
  rcases R with R | R | R
  · exact .of_compute (.base R)
  · exact (ComputeJoin.of_compute (.beta R.beta_back)).symm
  · exact (ComputeJoin.of_compute (.beta R.beta_back)).symm

/-- Full-union native guards still give a subrelation of the existing expanded
union. The ordinary roots and constant expansion are already stage zero. -/
theorem erased_core_expansion_into_union
    (R : ErasedCoreExpansion D (ErasedExpansionUnion D) Δ a b) : ErasedExpansionUnion D Δ a b := by
  rcases R with R | R | R
  · exact ⟨0, .inl (.inl R)⟩
  · exact ⟨0, .inr R⟩
  · exact erased_expansion_union_iff.2 (.inr (.inr (.inr R)))

/-- Every finite mixed path from a typed source has an exact ordinary-core
common reduct. Recursive definitions and computations inside retained domains
are allowed; no purity, normalization, or exact native-image premise appears. -/
theorem proofErase_core_expansion_join (hs : D.Sound env univs)
    (hr : ErasedScopedPrimitiveDescent Recovery) (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedCoreExpansion D Recovery) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputeJoin (ErasedIotaPrimitive D) (proofErase Γ e) out :=
  proofErase_scoped_compute_core_join (erased_core_expansion_descent hs hr) hc
    (fun R _ _ _ _ => erased_core_expansion_root_join R) R hΓ ht rfl rfl

/-- Independent mixed paths from one typed source meet using only ordinary
core reductions. Their native guard relations may differ. -/
theorem proofErase_core_expansion_confluent (hs : D.Sound env univs)
    (hr : ErasedScopedPrimitiveDescent Recovery) (hr' : ErasedScopedPrimitiveDescent Recovery')
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedCoreExpansion D Recovery) (proofEraseCtx Γ) (proofErase Γ e) a)
    (S : ScopedCompute (ErasedCoreExpansion D Recovery') (proofEraseCtx Γ) (proofErase Γ e) b) :
    ComputeJoin (ErasedIotaPrimitive D) a b :=
  (proofErase_core_expansion_join hs hr hc hΓ ht R).symm.trans_typed hc hΓ ht
    (proofErase_core_expansion_join hs hr' hc hΓ ht S)

/-- Arbitrary actual substitution preserves a whole mixed path up to a common
core reduct. It needs erasure agreement, but no exact or joined native images. -/
theorem proofErase_core_expansion_subst_join (hs : D.Sound env univs)
    (hr : ErasedScopedPrimitiveDescent Recovery) (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedCoreExpansion D Recovery) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputeJoin (ErasedIotaPrimitive D) (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  have H := (proofErase_core_expansion_join hs hr hc W.wf ht R).subst
    (fun H => erased_iota_primitive_subst H) (σ := τ)
  rwa [← proofErase_subst_with hΓ₀ W ht ES] at H

/-- A common-core family guard survives independent mixed paths at its typed
endpoints. Endpoint types need not coincide, and all residual computation stays
in the ordinary core rather than introducing a new recursive guard premise. -/
theorem proofErase_core_join_expansion_forward (hs : D.Sound env univs)
    (hr : ErasedScopedPrimitiveDescent Recovery) (hr' : ErasedScopedPrimitiveDescent Recovery')
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ComputeJoin (ErasedIotaPrimitive D) (proofErase Γ a) (proofErase Γ b))
    (RA : ScopedCompute (ErasedCoreExpansion D Recovery) (proofEraseCtx Γ) (proofErase Γ a) a')
    (RB : ScopedCompute (ErasedCoreExpansion D Recovery') (proofEraseCtx Γ) (proofErase Γ b) b') :
    ComputeJoin (ErasedIotaPrimitive D) a' b' :=
  ((proofErase_core_expansion_join hs hr hc hΓ ha RA).symm.trans_typed hc hΓ ha H).trans_typed
    hc hΓ hb (proofErase_core_expansion_join hs hr' hc hΓ hb RB)

namespace ErasedQuotCore
/-- The existing repaired-core confluence theorem discharges the target
hypothesis, including its registered proposition-source quotient equation. -/
theorem typed_core_confluence (hq : QuotRegistered env)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) : TypedCoreConfluence (Step hq) :=
  fun hΓ ht RA RB => confluent hq hcon hΓ ht RA RB

/-- Concrete mixed-path confluence with native guards from the entire expanded
union. No confluence or coverage of those native guards is assumed. -/
theorem expansion_confluent (hq : QuotRegistered env)
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedCoreExpansion (definitions hq) (ErasedExpansionUnion (definitions hq)))
      (proofEraseCtx Γ) (proofErase Γ e) a)
    (S : ScopedCompute (ErasedCoreExpansion (definitions hq) (ErasedExpansionUnion (definitions hq)))
      (proofEraseCtx Γ) (proofErase Γ e) b) : ComputeJoin (Step hq) a b :=
  proofErase_core_expansion_confluent (sound hq)
    (erased_expansion_union_descent heq (sound hq)) (erased_expansion_union_descent heq (sound hq))
    (typed_core_confluence hq hcon) hΓ ht R S

end ErasedQuotCore
end Lean4Lean.VEnv.Strengthening
