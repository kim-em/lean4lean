import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProjectionNativeJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonNativeEtaPivot

/-! # Dependent projection eta squares with a local recipe obligation

A historical major pivot and a beta contraction can meet at an arbitrary raw
major. Every dependent field recipe follows those paths. Joining the conversion
tail at the source recipe then supplies enough native information to join eta,
including a change of annotation. The source-recipe join remains an assumption.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Eta above any retained dependent projection commutes with a major beta
path, provided the source field recipe is confluent at its selected conversion
tail and the typed major pivot has the exact family certificate. The shared
major itself is raw. The local recipe joining premise is still unproved in
general; this is a conditional square, not a strengthening theorem or a claim
of strict reduction of the strengthening obligation. -/
theorem dependent_projection_eta_pivot_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (HT : ProjTele env univs s info ls doms result) (hj : info.nparams + j < doms.length)
    (ht : env.HasType univs Γ (.proj s j m) U) (hn : ¬ IsProof Γ (.proj s j m))
    (ht' : env.HasType univs Γ (.proj s j m') U') (hn' : ¬ IsProof Γ (.proj s j m'))
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const s ls) args))
    (hm' : env.HasType univs Γ m' (VExpr.mkApps (.const s ls) args))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ m') (ProofShape.mkApps (.const s ls) (args.map (proofErase Γ))))
    (Rbefore : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      original (proofErase Γ (.proj s j m')))
    (Rβ : ProofShape.BetaRed (proofErase Γ m) common)
    (R' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ m') common)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (projectionType s info doms j hj (args.map (proofErase Γ)) (proofErase Γ m))
      (proofErase Γ (.forallE A B)))
    (joinRecipe : ∀ {left right},
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (projectionType s info doms j hj (args.map (proofErase Γ)) (proofErase Γ m)) left →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (projectionType s info doms j hj (args.map (proofErase Γ)) (proofErase Γ m)) right →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) original shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.lam (proofErase Γ A)
          (.app ((proofErase Γ (.proj s j m)).liftN 1) (etaArgument u))) shared := by
  obtain ⟨T, RNT, RT⟩ := projection_native_tail_common heq hs hΓ hi HT hj
    ht hn ht' hn' hm hm' RN (.beta Rβ) R' RC joinRecipe
  have RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.proj s j m')) (.proj s j common) := by
    rw [show proofErase Γ (.proj s j m') = .proj s j (proofErase Γ m') from if_neg hn']
    exact .proj R'
  have RB : ProofShape.BetaRed (proofErase Γ (.proj s j m)) (.proj s j common) := by
    rw [show proofErase Γ (.proj s j m) = .proj s j (proofErase Γ m) from if_neg hn]
    exact .proj Rβ
  exact common_native_eta_pivot_square heq hs hΓ hA hB Rbefore RP RB RNT RT

end Lean4Lean.VEnv.Strengthening
