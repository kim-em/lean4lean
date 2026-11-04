import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStoredCoreConfluence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreExpansionConfluence

/-! # Common reducts with universe conversion and controlled beta expansion

Arbitrary finite interleavings of ordinary computation, universe conversion,
and constant/native identity expansion join in the universe-extended ordinary
core. Native guards may use a larger descending relation; no confluence of
those guards is assumed. Singleton roots remain outside this mixed fragment.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- The level core mixed with the two controlled beta-expansion primitives. -/
def ErasedLevelCoreExpansion (D : Definitions)
    (Recovery : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ErasedLevelCore D a b ∨ ConstantExpansion a b ∨ NativeIdentityExpansion Recovery Δ a b

/-- Native guard descent supplies source-typed descent for the whole mixture. -/
theorem erased_level_core_expansion_descent (hs : D.Sound env univs)
    (hr : ErasedScopedPrimitiveDescent Recovery) :
    ErasedScopedPrimitiveDescent (ErasedLevelCoreExpansion D Recovery) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  rcases R with R | R | R
  · exact erased_level_core_descent hs hΓ hΓ' W ht R
  · exact erased_constantExpansion_descent hΓ hΓ' W ht R
  · exact erased_nativeIdentityExpansion_descent hr hΓ hΓ' W ht R

/-- Every primitive has a common level-core reduct: expansion beta-contracts
back, so no transport of its native certificate is needed. -/
theorem erased_level_core_expansion_root_join
    (R : ErasedLevelCoreExpansion D Recovery Δ a b) : ComputeJoin (ErasedLevelCore D) a b := by
  rcases R with R | R | R
  · exact .of_compute (.base R)
  · exact (ComputeJoin.of_compute (.beta R.beta_back)).symm
  · exact (ComputeJoin.of_compute (.beta R.beta_back)).symm

/-- Full-union native guards place this mixture inside the existing expanded
union. Ordinary and level roots, and constant expansion, already occur at zero. -/
theorem erased_level_core_expansion_into_union
    (R : ErasedLevelCoreExpansion D (ErasedExpansionUnion D) Δ a b) :
    ErasedExpansionUnion D Δ a b := by
  rcases R with (R | R) | R | R
  · exact ⟨0, .inl (.inl R)⟩
  · exact ⟨0, .inl (.inr R)⟩
  · exact ⟨0, .inr R⟩
  · exact erased_expansion_union_iff.2 (.inr (.inr (.inr R)))

/-- The previous core/expansion fragment embeds without changing any guard. -/
theorem erased_core_expansion_into_level_core_expansion
    (R : ErasedCoreExpansion D Recovery Δ a b) : ErasedLevelCoreExpansion D Recovery Δ a b := by
  rcases R with R | R
  · exact .inl (.inl R)
  · exact .inr R

/-- Every finite mixed path is joined by level-core reductions, for arbitrary
source syntax and retained binder computations, without native-image premises. -/
theorem proofErase_level_core_expansion_join
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedLevelCoreExpansion D Recovery)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out :=
  proofErase_scoped_compute_core_join (erased_level_core_expansion_descent hs hr)
    (proofErase_level_core_confluent hs hlevels hcon hc)
    (fun R _ _ _ _ => erased_level_core_expansion_root_join R) R hΓ ht rfl rfl

/-- Independent mixed paths meet in the level core, even if their native guards
use different descending relations. Recursive definitions need not terminate. -/
theorem proofErase_level_core_expansion_confluent
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hr : ErasedScopedPrimitiveDescent Recovery) (hr' : ErasedScopedPrimitiveDescent Recovery')
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedLevelCoreExpansion D Recovery) (proofEraseCtx Γ) (proofErase Γ e) a)
    (S : ScopedCompute (ErasedLevelCoreExpansion D Recovery') (proofEraseCtx Γ) (proofErase Γ e) b) :
    ComputeJoin (ErasedLevelCore D) a b :=
  (proofErase_level_core_expansion_join hs hlevels hcon hc hr hΓ ht R).symm.trans_typed
    (proofErase_level_core_confluent hs hlevels hcon hc) hΓ ht
    (proofErase_level_core_expansion_join hs hlevels hcon hc hr' hΓ ht S)

/-- Universe-extended ordinary primitives are closed under arbitrary raw
substitution, independently of native recovery for the substitution images. -/
theorem erased_level_core_subst (R : ErasedLevelCore D a b) :
    ErasedLevelCore D (a.subst τ) (b.subst τ) := by
  rcases R with R | R
  · exact .inl (erased_iota_primitive_subst R)
  · exact .inr R.subst

/-- Actual substitution transports a whole mixed path up to an exact level-core
common reduct. Erasure agreement suffices; native-image recovery is not assumed. -/
theorem proofErase_level_core_expansion_subst_join
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedLevelCoreExpansion D Recovery) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputeJoin (ErasedLevelCore D) (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  have H := (proofErase_level_core_expansion_join hs hlevels hcon hc hr W.wf ht R).subst
    (fun H => erased_level_core_subst H) (σ := τ)
  rwa [← proofErase_subst_with hΓ₀ W ht ES] at H

/-- Common-core family guards survive independent mixed endpoint computation,
including universe conversion. The actual endpoint types may differ. -/
theorem proofErase_level_core_join_expansion_forward
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hr : ErasedScopedPrimitiveDescent Recovery) (hr' : ErasedScopedPrimitiveDescent Recovery')
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ComputeJoin (ErasedLevelCore D) (proofErase Γ a) (proofErase Γ b))
    (RA : ScopedCompute (ErasedLevelCoreExpansion D Recovery) (proofEraseCtx Γ) (proofErase Γ a) a')
    (RB : ScopedCompute (ErasedLevelCoreExpansion D Recovery') (proofEraseCtx Γ) (proofErase Γ b) b') :
    ComputeJoin (ErasedLevelCore D) a' b' :=
  ((proofErase_level_core_expansion_join hs hlevels hcon hc hr hΓ ha RA).symm.trans_typed
    (proofErase_level_core_confluent hs hlevels hcon hc) hΓ ha H).trans_typed
    (proofErase_level_core_confluent hs hlevels hcon hc) hΓ hb
    (proofErase_level_core_expansion_join hs hlevels hcon hc hr' hΓ hb RB)

namespace StoredCore
/-- For actual stored definitions, every core-confluence and universe-compatibility
premise is discharged. Native guards may use the entire existing expanded union. -/
theorem level_expansion_confluent (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedLevelCoreExpansion (Definitions.ofEnv env univs henv)
        (ErasedExpansionUnion (Definitions.ofEnv env univs henv)))
      (proofEraseCtx Γ) (proofErase Γ e) a)
    (S : ScopedCompute (ErasedLevelCoreExpansion (Definitions.ofEnv env univs henv)
        (ErasedExpansionUnion (Definitions.ofEnv env univs henv)))
      (proofEraseCtx Γ) (proofErase Γ e) b) :
    ComputeJoin (ErasedLevelCore (Definitions.ofEnv env univs henv)) a b :=
  proofErase_level_core_expansion_confluent (Definitions.ofEnv_sound henv)
    (Definitions.ofEnv_levelCompatible henv) hcon (typed_core_confluence hcon)
    (erased_expansion_union_descent heq (Definitions.ofEnv_sound henv))
    (erased_expansion_union_descent heq (Definitions.ofEnv_sound henv)) hΓ ht R S
end StoredCore
end Lean4Lean.VEnv.Strengthening
