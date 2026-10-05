import Lean4Lean.Theory.Typing.TypedWorldProofSubstitution
import Lean4Lean.Theory.Typing.TypedWorldProofReadback

/-! Canonical, history-independent proof-slot copying. The literal output
context and readback are computed from the total insertion, not from a chosen
decomposition into generated and later proof slots. -/
namespace Lean4Lean.VEnv
open VExpr
set_option backward.isDefEq.respectTransparency false

theorem ProofInsertion.mapSubstitution_exact
    {env : VEnv} {U : Nat} (henv : env.Ordered)
    {Δ Ω : List VExpr} {τ : Lift} (insertion : ProofInsertion env U Δ Ω τ)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {σ : Subst}
    (typed : Ctx.SubstEq env U Γ σ σ Δ) :
    ProofInsertion env U Γ (replayContext Γ Ω τ σ) (.skipN .refl (proofCount τ)) ∧
    Ctx.SubstEq env U (replayContext Γ Ω τ σ)
      (proofReadback τ σ) (proofReadback τ σ) Ω ∧
    (∀ e : VExpr, (e.lift' τ).subst (proofReadback τ σ) =
      (e.subst σ).liftN (proofCount τ)) := by
  suffices result : ProofInsertion env U Γ (replayContext Γ Ω τ σ)
      (.skipN .refl (proofCount τ)) ∧
      Ctx.SubstEq env U (replayContext Γ Ω τ σ)
        (proofReadback τ σ) (proofReadback τ σ) Ω by
    refine ⟨result.1, result.2, fun e => ?_⟩
    exact (proofReadback_commute τ σ e).trans (lift'_consN_skipN (k := 0))
  induction insertion generalizing Γ σ with
  | refl =>
    simpa only [replayContext, proofCount, proofReadback, Lift.depth, Lift.skipN]
      using And.intro (ProofInsertion.refl hΓ) typed
  | @skip Δ Ω τ P q previous hP hq ih =>
    obtain ⟨frame, substituted⟩ := ih hΓ typed
    have hP' := hP.subst henv substituted (frame.targetWF henv)
    have hq' := hq.subst henv substituted (frame.targetWF henv)
    exact ⟨frame.skip hP' hq', substituted.lift henv hP⟩
  | @cons Δ Ω τ A u previous hA ih =>
    cases typed with
    | cons typed hA' head =>
      obtain ⟨frame, substituted⟩ := ih hΓ typed
      have changed : (A.lift' τ).subst (proofReadback τ σ.tail) =
          (A.subst σ.tail).liftN (proofCount τ) :=
        (proofReadback_commute τ σ.tail A).trans (lift'_consN_skipN (k := 0))
      have head' := head.weak' henv frame.weakening
      have newTyped : Ctx.SubstEq env U (replayContext Γ Ω τ σ.tail)
          (proofReadback τ.cons σ) (proofReadback τ.cons σ) (A.lift' τ :: Ω) := by
        refine .cons substituted (hA.weak' henv previous.weakening) ?_
        change env.IsDefEq U _ (σ.head.liftN (proofCount τ)) (σ.head.liftN (proofCount τ))
          ((A.lift' τ).subst (proofReadback τ σ.tail))
        rw [changed]
        simpa only [show ∀ e : VExpr, e.lift' (.skipN .refl (proofCount τ)) =
          e.liftN (proofCount τ) from fun e => lift'_consN_skipN (k := 0)] using head'
      exact ⟨frame, newTyped⟩

/-- Complete a caller-selected replay world and readback to a split proof
section. The replay world may have undergone terminal context conversion:
its inclusion need only be a future insertion, while the resulting section
is still an actual proof insertion. -/
theorem SplitTypedEmbedding.extendProofWith
    {env : VEnv} {U : Nat} {Γ Δ Ω V : List VExpr} {τ κ : Lift}
    (F : SplitTypedEmbedding env U Γ Δ)
    (proofSection : ProofInsertion env U Γ Δ F.liftMap)
    (post : ProofInsertion env U Δ Ω τ) (henv : env.Ordered)
    (smallFrame : FutureInsertion env U Γ V κ) (σ : Subst)
    (typed : Ctx.SubstEq env U V σ σ Ω)
    (commute : ∀ e : VExpr, (e.lift' τ).subst σ = (e.subst F.retract).lift' κ) :
    ∃ W j, FutureInsertion env U Ω W j ∧
      ∃ G : SplitTypedEmbedding env U V W,
        ProofInsertion env U V W G.liftMap ∧
        Subst.lift_l j G.retract = σ ∧
        (F.liftMap.comp τ).comp j = κ.comp G.liftMap := by
  obtain ⟨M⟩ := (proofSection.comp post henv).amalgam smallFrame henv
  have agree : Subst.lift_l (F.liftMap.comp τ) σ = Subst.lift_l κ Subst.id := by
    funext i
    have hi := F.leftInv (.bvar i)
    have h := commute ((VExpr.bvar i).lift' F.liftMap)
    change F.retract (F.liftMap.liftVar i) = .bvar i at hi
    change σ (τ.liftVar (F.liftMap.liftVar i)) =
      (F.retract (F.liftMap.liftVar i)).lift' κ at h
    change σ ((F.liftMap.comp τ).liftVar i) = .bvar (κ.liftVar i)
    rw [Lift.liftVar_comp, h, hi]
    rfl
  obtain ⟨retract, left, right⟩ := M.merge σ Subst.id agree
  have mergedTyped : Ctx.SubstEq env U V retract retract M.context := by
    apply M.typing
    · rw [left]; exact typed
    · rw [right]; exact .id henv (smallFrame.targetWF henv)
  let G := M.proof.withRetraction henv retract mergedTyped
    (by intro e; rw [subst_lift', right, subst_id])
  exact ⟨M.context, M.rightMap, M.future, G, M.proof, left, M.commute⟩

/-- Canonical specialization: the small world, base map and old-world
readback are literal functions of the complete original insertion. -/
theorem SplitTypedEmbedding.extendProof_exact
    {env : VEnv} {U : Nat} {Γ Δ Ω : List VExpr} {τ : Lift}
    (F : SplitTypedEmbedding env U Γ Δ)
    (proofSection : ProofInsertion env U Γ Δ F.liftMap)
    (post : ProofInsertion env U Δ Ω τ) (henv : env.Ordered) :
    ∃ W j, FutureInsertion env U Ω W j ∧
      ∃ G : SplitTypedEmbedding env U (replayContext Γ Ω τ F.retract) W,
        ProofInsertion env U (replayContext Γ Ω τ F.retract) W G.liftMap ∧
        Subst.lift_l j G.retract = proofReadback τ F.retract ∧
        (F.liftMap.comp τ).comp j =
          (Lift.skipN .refl (proofCount τ)).comp G.liftMap := by
  obtain ⟨frame, typed, _⟩ := post.mapSubstitution_exact henv F.baseWF F.typed
  exact F.extendProofWith proofSection post henv frame.toFuture _ typed
    (proofReadback_commute τ F.retract)

end Lean4Lean.VEnv
