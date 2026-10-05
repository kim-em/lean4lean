import Lean4Lean.Theory.Typing.TypedWorld

/-! Typed substitutions through a proof insertion are determined, up to raw
equality, by their restriction to its base. Every discarded slot is an actual
proposition; this is not arbitrary context strengthening. -/
namespace Lean4Lean.VEnv
open VExpr
set_option backward.isDefEq.respectTransparency false

/-- The two substitutions may choose different inhabitants of every inserted
proof type. Agreement on retained variables suffices for typed equality. -/
theorem ProofInsertion.compareSubstitutions
    (H : ProofInsertion env U Γ Δ ρ) (henv : env.Ordered)
    (hTarget : OnCtx target (env.IsType U))
    (left : Ctx.SubstEq env U target σ σ Δ)
    (right : Ctx.SubstEq env U target τ τ Δ)
    (base : Ctx.SubstEq env U target (Subst.lift_l ρ σ) (Subst.lift_l ρ τ) Γ) :
    Ctx.SubstEq env U target σ τ Δ := by
  induction H generalizing σ τ with
  | refl => exact base
  | @skip Γ Δ ρ P q previous formed witness ih =>
    cases left with
    | cons leftTail _ leftHead =>
      cases right with
      | cons rightTail _ rightHead =>
        have tails := ih leftTail rightTail base
        have proposition := formed.subst henv leftTail hTarget
        have domains := formed.substDF henv (previous.targetWF henv) hTarget tails
        refine .cons tails formed ?_
        exact .proofIrrel proposition leftHead (.defeqDF domains.symm rightHead)
  | @cons Γ Δ ρ A u previous formed ih =>
    cases left with
    | cons leftTail _ _ =>
      cases right with
      | cons rightTail _ _ =>
        cases base with
        | cons baseTail _ baseHead =>
          refine .cons (ih leftTail rightTail baseTail)
            (formed.weak' henv previous.weakening) ?_
          have tails (f : Subst) :
              (Subst.lift_l ρ.cons f).tail = Subst.lift_l ρ f.tail := rfl
          simpa only [subst_lift', tails, Subst.head, Subst.lift_l, Lift.liftVar] using baseHead

/-- Any chosen typed left inverse of an actual proof insertion has the raw
reverse inverse as well. This permits choosing existing proof variables as
retraction witnesses instead of the insertion's original inhabitants. -/
def ProofInsertion.withRetraction
    (H : ProofInsertion env U Γ Δ ρ) (henv : env.Ordered)
    (σ : Subst) (typed : Ctx.SubstEq env U Γ σ σ Δ)
    (inverse : ∀ e : VExpr, (e.lift' ρ).subst σ = e) :
    SplitTypedEmbedding env U Γ Δ where
  liftMap := ρ
  retract := σ
  weakening := H.typedRenaming henv
  typed := typed
  leftInv := inverse
  rightInv := by
    apply H.compareSubstitutions henv (H.targetWF henv)
      (.id henv (H.targetWF henv)) (typed.weakenTarget henv H.weakening)
    have baseEq : Subst.lift_l ρ (σ.lift_r ρ) = Subst.id.lift_r ρ := by
      funext i
      have h := inverse (.bvar i)
      change σ (ρ.liftVar i) = .bvar i at h
      change (σ (ρ.liftVar i)).lift' ρ = (VExpr.bvar i).lift' ρ
      rw [h]
    rw [baseEq]
    exact H.typedRenaming henv

end Lean4Lean.VEnv
