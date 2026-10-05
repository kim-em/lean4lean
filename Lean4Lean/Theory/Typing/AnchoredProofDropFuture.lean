import Lean4Lean.Theory.Typing.AnchoredProofDropFunction
import Lean4Lean.Theory.Typing.TypedWorldAmalgamation

/-! The arbitrary-future square is generated from one actual projected Pi
frame. No second trace projection or independently chosen retraction occurs. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem subst_cons_square (e : VExpr) (ρ τ : Lift) (σ υ : Subst)
    (square : Subst.lift_l ρ σ = υ.lift_r τ) :
    (e.lift' ρ.cons).subst σ.lift = (e.subst υ.lift).lift' τ.cons := by
  rw [subst_lift', lift'_subst]
  apply congrArg (e.subst ·)
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    have h := congrFun square i
    change (σ (ρ.liftVar i)).lift = (υ i).lift.lift' τ.cons
    change σ (ρ.liftVar i) = (υ i).lift' τ at h
    rw [h]
    simp only [lift_eq_lift', ← lift'_comp, Lift.comp, Lift.refl_comp]

/-- Exact raw identities at one projected display suffice for all future
worlds, including fresh data binders. -/
theorem ProofDropPiFrame.futures
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered)
    {Γsmall Γlarge : List VExpr} {initial : SplitTypedEmbedding env U Γsmall Γlarge}
    {left right A B : VExpr} {domain : Profile n} {rows : List (Key n × Profile n)}
    {small : RawPiDisplay env U registry Γsmall
      (left.subst initial.retract) (right.subst initial.retract) A B}
    {large : PiWitness env U registry (relations env U registry n)
      Γlarge left right (A.lift' initial.liftMap) (B.lift' initial.liftMap.cons)
      (domain.rename initial.liftMap) (Rows.rename initial.liftMap rows)}
    (base : ProofDropPiFrame env U registry initial.liftMap small large)
    (operands : ∀ e : VExpr,
      (e.lift' (large.map.comp base.postMap)).subst base.frame.retract =
        (e.subst initial.retract).lift' small.map)
    (leftBody : (large.leftBody.lift' base.postMap.cons).subst base.frame.retract.lift =
      small.leftBody)
    (rightBody : (large.rightBody.lift' base.postMap.cons).subst base.frame.retract.lift =
      small.rightBody)
    (Δ : List VExpr) (ρ : Lift) (future : FutureInsertion env U small.context Δ ρ) :
    Nonempty { square : ProofDropPiFuture env U registry initial.liftMap small large Δ ρ //
      ∀ e : VExpr,
        (e.lift' (large.map.comp square.oldMap)).subst square.frame.retract =
          (e.subst initial.retract).lift' (small.map.comp ρ) } := by
  obtain ⟨W, i, j, proof, largerFuture, maps, next, nextMap, nextRetract⟩ :=
    base.frame.pushoutChosen base.insertion future henv
  subst i
  obtain ⟨oldWorld, oldFuture, changed⟩ := base.changed.pullFuture henv largerFuture
  let square : ProofDropPiFuture env U registry initial.liftMap small large Δ ρ := {
    oldWorld := oldWorld
    oldMap := base.postMap.comp j
    oldFuture := base.post.comp oldFuture henv
    largeWorld := W
    changed := changed
    frame := next
    insertion := proof
    square := by
      calc
        initial.liftMap.comp (large.map.comp (base.postMap.comp j)) =
            (initial.liftMap.comp (large.map.comp base.postMap)).comp j := by
          simp only [Lift.comp_assoc]
        _ = (small.map.comp ρ).comp next.liftMap := by
          rw [base.square, Lift.comp_assoc, maps, ← Lift.comp_assoc]
    leftBody := by
      change (large.leftBody.lift' (base.postMap.cons.comp j.cons)).subst next.retract.lift = _
      rw [lift'_comp, subst_cons_square _ j ρ next.retract base.frame.retract nextRetract,
        leftBody]
    rightBody := by
      change (large.rightBody.lift' (base.postMap.cons.comp j.cons)).subst next.retract.lift = _
      rw [lift'_comp, subst_cons_square _ j ρ next.retract base.frame.retract nextRetract,
        rightBody] }
  refine ⟨⟨square, ?_⟩⟩
  intro e
  change (e.lift' (large.map.comp (base.postMap.comp j))).subst next.retract = _
  rw [← Lift.comp_assoc, lift'_comp, subst_lift', nextRetract, ← lift'_subst,
    operands, ← lift'_comp]

/-- Assemble the complete raw projection package from its single base frame. -/
def ProofDropPiProjection.ofFrame
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered)
    {Γsmall Γlarge : List VExpr} {initial : SplitTypedEmbedding env U Γsmall Γlarge}
    {left right A B : VExpr} {domain : Profile n} {rows : List (Key n × Profile n)}
    (small : RawPiDisplay env U registry Γsmall
      (left.subst initial.retract) (right.subst initial.retract) A B)
    {large : PiWitness env U registry (relations env U registry n)
      Γlarge left right (A.lift' initial.liftMap) (B.lift' initial.liftMap.cons)
      (domain.rename initial.liftMap) (Rows.rename initial.liftMap rows)}
    (base : ProofDropPiFrame env U registry initial.liftMap small large)
    (operands : ∀ e : VExpr,
      (e.lift' (large.map.comp base.postMap)).subst base.frame.retract =
        (e.subst initial.retract).lift' small.map)
    (leftBody : (large.leftBody.lift' base.postMap.cons).subst base.frame.retract.lift =
      small.leftBody)
    (rightBody : (large.rightBody.lift' base.postMap.cons).subst base.frame.retract.lift =
      small.rightBody) : ProofDropPiProjection env U registry initial large where
  raw := small
  frame := base
  futures := base.futures henv operands leftBody rightBody

end Lean4Lean.AnchoredSemantics
