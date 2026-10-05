import Lean4Lean.Theory.Typing.AnchoredExposureDrop
import Lean4Lean.Theory.Typing.TypedWorldProofContext
import Lean4Lean.Theory.Typing.TypedWorldProofPrefix

/-! Exposures projected into one canonical complement context. The output
context, map and head readback depend only on the original endpoint and map,
not on the decomposition of a trace into generated and post proof slots. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false

theorem Exposure.projectCanonical
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ Ω : List VExpr} {ρ : Lift} {expression head : VExpr} {σ : Subst}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U)) (typed : Ctx.SubstEq env U Γ σ σ Δ)
    (E : Exposure env U registry Δ expression Ω ρ head) :
    Nonempty (Exposure env U registry Γ (expression.subst σ)
      (replayContext Γ Ω ρ σ) (.skipN .refl (proofCount ρ))
      (head.subst (proofReadback ρ σ))) := by
  have total : ProofInsertion env U Δ E.postContext ρ := by
    simpa only [E.map_eq] using E.generated.comp E.post henv
  obtain ⟨frame, readback, _⟩ := total.mapSubstitution_exact henv hΓ typed
  have changed := E.terminal.replayContext henv total hΓ typed
  obtain ⟨front, _⟩ := E.generated.substFront henv hΓ typed E.added
  have post := ProofInsertion.mapSubstitutionWithPrefix henv hΓ typed E.added E.generated E.post
  rw [E.map_eq] at post
  have sound := ((E.terminal.symm henv).path henv E.sound).substTarget henv
    (frame.targetWF henv) readback
  rw [proofReadback_commute] at sound
  have headType := ((E.terminal.symm henv).isType henv E.headType).subst henv
    readback (frame.targetWF henv)
  refine ⟨{
    added := substAdded σ E.added
    result := E.result.subst (σ.liftN E.added.length)
    postMap := proofFrontMap E.added.length E.postMap
    trace := E.trace.subst hscoped σ
    generated := by simpa only [substAdded_length] using front
    postContext := replayContext Γ E.postContext ρ σ
    post := post
    terminal := changed
    map_eq := ?_
    result_eq := ?_
    sound := changed.path henv sound
    headType := changed.isType henv headType }⟩
  · rw [substAdded_length, proofFrontMap_base]
    have counts := congrArg VEnv.proofCount E.map_eq
    simp only [VEnv.proofCount, Lift.depth_comp, Lift.depth_skipN, Lift.depth, Nat.zero_add] at counts
    exact congrArg (Lift.skipN .refl) counts
  · have result := proofReadback_front E.added.length E.postMap σ E.result
    rw [E.map_eq, E.result_eq] at result
    exact result.symm

end Lean4Lean.AnchoredSemantics
