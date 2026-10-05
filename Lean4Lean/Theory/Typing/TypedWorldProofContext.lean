import Lean4Lean.Theory.Typing.TypedWorldProofSubstitutionExact
import Lean4Lean.Theory.Typing.TypedWorldMixed

/-! Project a terminal context conversion without assuming that its converted
proof domains still have universe zero. The raw head conversion stays at the
original tail, where the chosen canonical readback is already typed. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

private theorem ContextChain.peel
    (henv : env.Ordered) (chain : ContextChain env U source target) :
    ∀ {A Γ}, source = A :: Γ → ∃ B Δ, target = B :: Δ ∧
      ContextChain env U Γ Δ ∧ TypeConversion env U Γ A B := by
  induction chain with
  | refl =>
    intro A Γ equal
    exact ⟨A, Γ, equal, .refl, .refl⟩
  | @tail middle target previous edge ih =>
    intro A Γ equal
    obtain ⟨B, Δ, middleEq, tails, heads⟩ := ih equal
    subst middle
    cases edge with
    | succ tailEdge headEdge =>
      exact ⟨_, _, rfl, .tail tails tailEdge,
        .tail heads ((tails.symm henv).eq henv headEdge)⟩

/-- Inverting a chain exposes a path of head domains at the original tail;
individual edges may use different universes and changed tail declarations. -/
theorem ContextChain.cons_inv
    (henv : env.Ordered) (chain : ContextChain env U (A :: Γ) (B :: Δ)) :
    ContextChain env U Γ Δ ∧ TypeConversion env U Γ A B := by
  obtain ⟨B', Δ', equal, tails, heads⟩ := chain.peel henv rfl
  cases equal
  exact ⟨tails, heads⟩

/-- Lift the actual finite head-domain path into a context path. -/
theorem ContextChain.changeHead
    (hΓ : OnCtx Γ (env.IsType U)) (path : TypeConversion env U Γ A B) :
    ContextChain env U (A :: Γ) (B :: Γ) := by
  induction path with
  | refl => exact .refl
  | tail _ edge ih => exact .tail ih (.succ (.refl hΓ) edge)

private theorem TypeConversion.targetIsType
    (path : TypeConversion env U Γ A B) (formed : env.IsType U Γ A) :
    env.IsType U Γ B := by
  cases path with
  | refl => exact formed
  | tail _ edge => exact ⟨_, edge.hasType.2⟩

/-- Terminal context conversion commutes with the canonical complete-history
copy. Only the original proof insertion supplies inhabitants; the converted
endpoint is reached by a context chain, without reclassifying its universes. -/
theorem ContextChain.replayContext
    {env : VEnv} {U : Nat} {source oldTarget newTarget base : List VExpr}
    {ρ : Lift} {σ : Subst}
    (henv : env.Ordered) (insertion : ProofInsertion env U source oldTarget ρ)
    (hBase : OnCtx base (env.IsType U))
    (typed : Ctx.SubstEq env U base σ σ source)
    (chain : ContextChain env U oldTarget newTarget) :
    ContextChain env U (VEnv.replayContext base oldTarget ρ σ)
      (VEnv.replayContext base newTarget ρ σ) := by
  induction insertion generalizing σ newTarget with
  | refl => simpa only [VEnv.replayContext] using (ContextChain.refl : ContextChain env U base base)
  | @skip source oldTarget ρ P q previous formed witness ih =>
    obtain ⟨P', tail', equal, tails, heads⟩ := chain.peel henv rfl
    subst newTarget
    obtain ⟨frame, readback, _⟩ := previous.mapSubstitution_exact henv hBase typed
    have hTail := frame.targetWF henv
    have projectedHeads := heads.substTarget henv hTail readback
    have projectedTails := ih typed tails
    have lastType := TypeConversion.targetIsType projectedHeads
      ⟨_, formed.subst henv readback hTail⟩
    exact (ContextChain.changeHead hTail projectedHeads).trans
      (projectedTails.underBinder henv lastType)
  | @cons source oldTarget ρ A u previous formed ih =>
    obtain ⟨A', tail', equal, tails, _⟩ := chain.peel henv rfl
    subst newTarget
    cases typed with
    | cons tailTyped _ _ => exact ih tailTyped tails

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.VEnv
open VExpr AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Change target declarations without changing a substitution's terms. -/
theorem Ctx.SubstEq.targetChain
    (henv : env.Ordered) (chain : ContextChain env U target target')
    (typed : Ctx.SubstEq env U target σ τ source) :
    Ctx.SubstEq env U target' σ τ source := by
  induction typed with
  | nil => exact .nil
  | cons _ formed head ih => exact .cons ih formed (chain.eq henv head)

/-- Compose a raw substitution with a diagonal typed target substitution. -/
theorem Ctx.SubstEq.substTarget
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (typed : Ctx.SubstEq env U middle σ τ source)
    (after : Ctx.SubstEq env U target υ υ middle) :
    Ctx.SubstEq env U target (σ.comp υ) (τ.comp υ) source := by
  induction typed with
  | nil => exact .nil
  | cons _ formed head ih =>
    refine .cons ih formed ?_
    have h := head.subst henv after hTarget
    have tails (a b : Subst) : (a.comp b).tail = a.tail.comp b := rfl
    have heads (a b : Subst) : (a.comp b).head = a.head.subst b := rfl
    simpa only [subst_subst, tails, heads] using h

/-- Change source declarations using their actual typed context chain. -/
theorem Ctx.SubstEq.sourceChain
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (chain : ContextChain env U source source')
    (typed : Ctx.SubstEq env U target σ σ source) :
    Ctx.SubstEq env U target σ σ source' := by
  have identity := (Ctx.SubstEq.id henv (chain.targetWF henv typed.wf)).targetChain
    henv (chain.symm henv)
  have composed := identity.substTarget henv hTarget typed
  have identityComp : Subst.id.comp σ = σ := by funext i; rfl
  rwa [identityComp] at composed

end Lean4Lean.VEnv

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

/-- Canonical readback remains typed after projecting the terminal context
chain, on both the source and target sides of the substitution. -/
theorem ContextChain.replayTyped
    {env : VEnv} {U : Nat} {source oldTarget newTarget base : List VExpr}
    {ρ : Lift} {σ : Subst}
    (henv : env.Ordered) (insertion : ProofInsertion env U source oldTarget ρ)
    (hBase : OnCtx base (env.IsType U))
    (typed : Ctx.SubstEq env U base σ σ source)
    (chain : ContextChain env U oldTarget newTarget) :
    Ctx.SubstEq env U (VEnv.replayContext base newTarget ρ σ)
      (proofReadback ρ σ) (proofReadback ρ σ) newTarget := by
  obtain ⟨frame, readback, _⟩ := insertion.mapSubstitution_exact henv hBase typed
  have projected := chain.replayContext henv insertion hBase typed
  exact (readback.targetChain henv projected).sourceChain henv
    (projected.targetWF henv (frame.targetWF henv)) chain

/-- The final copied context retains the original base literally. Converted
copy slots may be ordinary types, so this is a future insertion. -/
theorem ContextChain.replayFuture
    {env : VEnv} {U : Nat} {source oldTarget newTarget base : List VExpr}
    {ρ : Lift} {σ : Subst}
    (henv : env.Ordered) (insertion : ProofInsertion env U source oldTarget ρ)
    (hBase : OnCtx base (env.IsType U))
    (typed : Ctx.SubstEq env U base σ σ source)
    (chain : ContextChain env U oldTarget newTarget) :
    FutureInsertion env U base (VEnv.replayContext base newTarget ρ σ)
      (.skipN .refl (proofCount ρ)) := by
  induction insertion generalizing σ newTarget with
  | refl => simpa only [VEnv.replayContext, proofCount, Lift.depth, Lift.skipN] using
      (FutureInsertion.refl hBase)
  | @skip source oldTarget ρ P q previous formed witness ih =>
    obtain ⟨P', tail', equal, tails, _⟩ := chain.peel henv rfl
    subst newTarget
    have wf := (chain.replayContext henv (previous.skip formed witness) hBase typed).targetWF
      henv (((previous.skip formed witness).mapSubstitution_exact henv hBase typed).1.targetWF henv)
    obtain ⟨_, level, head⟩ := wf
    exact (ih typed tails).skip head
  | @cons source oldTarget ρ A u previous formed ih =>
    obtain ⟨A', tail', equal, tails, _⟩ := chain.peel henv rfl
    subst newTarget
    cases typed with
    | cons tailTyped _ _ => exact ih tailTyped tails

end Lean4Lean.AnchoredSemantics
