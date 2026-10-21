import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureCarrierPrefixes

/-! # Arbitrary domain changes for retained future function bodies

An explicit future body certificate already transports through interpreted
context conversion. Consequently a function recipe can change its domain along
any actual type equality, or any sound primitive computation. No recovered
type resynthesis is needed. The body certificate is an input: it is not inferred
from a whole-function certificate or arbitrary declarative equality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- The stored substitution futures include the interpreted identity between
equal actual contexts. Raw endpoints remain unchanged, and all later beta and
substitution futures are retained. No primitive closure hypothesis is needed. -/
theorem BetaStableFamily.defeqCtx
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs Γ Γ₁ Γ₂)
    (H : BetaStableFamily R (proofEraseCtx Γ₁) a b) :
    BetaStableFamily R (proofEraseCtx Γ₂) a b := by
  simpa only [ProofShape.subst_id] using H.subst (ContextSubstitution.of_defeqCtx hΓ W)

/-- Equal-context interpretation transports carrier futures as well, keeping
the raw carrier and endpoints fixed. This consumes the full future certificate,
not a general context-conversion law for ordinary joint checking. -/
theorem BetaStableCarrier.defeqCtx
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs Γ Γ₁ Γ₂)
    (H : BetaStableCarrier Step (proofEraseCtx Γ₁) C a b) :
    BetaStableCarrier Step (proofEraseCtx Γ₂) C a b := by
  simpa only [ProofShape.subst_id] using H.subst (ContextSubstitution.of_defeqCtx hΓ W)

/-- A retained future eta-body recipe supports any actual equal-domain change,
including arbitrary primitive changes. Its raw codomain remains fixed while
the body context changes. The target certificate retains independent domain,
codomain and endpoint beta paths and every interpreted substitution. -/
theorem BetaStableCarrier.function_defeq_domain
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A A' (.sort u))
    (H : BetaStableCarrier Step (proofEraseCtx (A :: Γ)) B
      (.app (a.liftN 1) (etaArgument u)) (.app (b.liftN 1) (etaArgument u))) :
    BetaStableCarrier Step (proofEraseCtx Γ) (.forallE (proofErase Γ A') B) a b := by
  have HC := H.defeqCtx hΓ (IsDefEqCtx.succ .zero HE)
  exact HC.function ⟨Γ, A', hΓ, rfl, HE.hasType.2, rfl⟩

/-- Sound primitive domain computation changes a function carrier when its
future eta-body certificate is retained. The computed domain may have any raw
shape. Computation and checking relations are independent, and neither
confluence nor an inverse weakening or general carrier-conversion premise is
used. Only the domain is replayed to obtain its equal actual representative. -/
theorem BetaStableCarrier.function_computed_domain
    (hstep : ErasedScopedPrimitiveDescent ComputeStep)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (R : ScopedCompute ComputeStep (proofEraseCtx Γ) (proofErase Γ A) A')
    (H : BetaStableCarrier Step (proofEraseCtx (A :: Γ)) B
      (.app (a.liftN 1) (etaArgument u)) (.app (b.liftN 1) (etaArgument u))) :
    BetaStableCarrier Step (proofEraseCtx Γ) (.forallE A' B) a b := by
  obtain ⟨A₁, HE, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA rfl rfl R
  simpa only [EA] using H.function_defeq_domain hΓ HE

end Lean4Lean.VEnv.Strengthening
