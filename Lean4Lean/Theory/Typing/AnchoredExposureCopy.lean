import Lean4Lean.Theory.Typing.AnchoredExposureClone
import Lean4Lean.Theory.Typing.TypedWorldProofCopy
import Lean4Lean.Theory.Typing.TypedWorldProofContext

/-! Contract the actual fresh type-display prefix onto the chosen existing
display variables. The existing copy is obtained from the original exposure
and its actual future, not supplied as a semantic equality hypothesis. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false

theorem Exposure.piCopyRetraction
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Ω Δ Ξ : List VExpr} {expression A B A' B' : VExpr} {map ρ map' : Lift}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (original : Exposure env U registry Γ expression Ω map (.forallE A B))
    (future : FutureInsertion env U Ω Δ ρ)
    (replayed : Exposure env U registry Δ (expression.lift' (map.comp ρ))
      Ξ map' (.forallE A' B')) :
    ∃ F : SplitTypedEmbedding env U Δ
        (renameAdded (map.comp ρ) original.added ++ Δ),
      F.liftMap = .skipN .refl original.added.length ∧
      replayed.added = renameAdded (map.comp ρ) original.added ∧
      (∀ e : VExpr,
        (e.lift' ((map.comp ρ).consN original.added.length)).subst F.retract =
          e.lift' (original.postMap.comp ρ)) ∧
      replayed.result.subst F.retract = (.forallE A B : VExpr).lift' ρ := by
  obtain ⟨front, result⟩ := original.piTrace_renamed hscoped replayed
  let values : Subst := Subst.id.lift_r (original.postMap.comp ρ)
  have typed : Ctx.SubstEq env U Δ values values (original.added ++ Γ) := by
    have old := (original.post.typedRenaming henv).targetChain henv original.terminal
    have moved := old.weakenTarget henv future.weakening
    have same : (Subst.id.lift_r original.postMap).lift_r ρ = values := by
      funext i
      exact lift'_comp.symm
    rw [same] at moved
    exact moved
  have base : Subst.lift_l (.skipN .refl original.added.length) values =
      Subst.id.lift_r (map.comp ρ) := by
    funext i
    change VExpr.bvar ((original.postMap.comp ρ).liftVar
        ((Lift.skipN .refl original.added.length).liftVar i)) =
      .bvar ((map.comp ρ).liftVar i)
    rw [← Lift.liftVar_comp, ← Lift.comp_assoc, original.map_eq]
  have generated : ProofInsertion env U Δ
      (renameAdded (map.comp ρ) original.added ++ Δ)
      (.skipN .refl original.added.length) := by
    simpa only [front, renameAdded_length] using replayed.generated
  let F := generated.copyRetraction henv original.added typed base
  have copy (e : VExpr) :
      (e.lift' ((map.comp ρ).consN original.added.length)).subst F.retract =
        e.lift' (original.postMap.comp ρ) := by
    change (e.lift' ((map.comp ρ).consN original.added.length)).subst
      (proofCopyReadback values original.added.length) = _
    rw [subst_lift', proofCopyReadback_copy values original.added.length (map.comp ρ) base]
    simp only [values, ← lift'_subst, subst_id]
  refine ⟨F, rfl, front, copy, ?_⟩
  rw [result, copy, lift'_comp, original.result_eq]

end Lean4Lean.AnchoredSemantics
