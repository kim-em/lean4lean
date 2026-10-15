import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedFinitePairedFront
import Lean4Lean.Theory.Typing.UnitLikeConstructor

/-! # A typed empty-structure gap at every scoped computation stage

Two distinct variables of a non-propositional unit-like family are equal by the
original unitLike rule. Each compares with the actual typed constructor, but the
variables cannot compare directly in ScopedCompare. Additional singleton stages
cannot help: primitives never compute a variable head.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout

/-- Constant/projection-headed primitives leave a bare variable fixed through
all finite compatible computations, including under contextual stage guards. -/
theorem ProofShape.ScopedCompute.bvar_fixed
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (.bvar i) out) : out = .bvar i :=
  scoped_normal_fixed R (fun _ => ⟨fun _ H => hhead H, trivial⟩)

variable [Params]
/-- Distinct variables have no scoped comparison certificate in either mode,
regardless of how many constant/projection-headed computation rules are added. -/
theorem ProofShape.ScopedCompare.bvar_injective
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : ScopedCompare Step Δ mode (.bvar i) (.bvar j)) : i = j := by
  generalize EA : ProofShape.bvar i = a at H
  generalize EB : ProofShape.bvar j = b at H
  induction H generalizing i j with
  | leaf H =>
    cases H with
    | refl => exact ProofShape.bvar.inj (EA.trans EB.symm)
    | sort | const => cases EA
    | etaL H => obtain ⟨_, _, E, _⟩ := H.shape; cases EA.trans E
    | etaR H => obtain ⟨_, _, E, _⟩ := H.shape; cases EB.trans E
  | compute RA RB H ih =>
    exact ih ((EA ▸ RA).bvar_fixed hhead).symm ((EB ▸ RB).bvar_fixed hhead).symm
  | symm H ih => exact (ih EB EA).symm
  | structFields =>
    have E := congrArg ProofShape.constHead EA
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  | etaBodyR => cases EB
  | app | proj | lam | forallE | lamSorted | forallSorted | lamCommon | etaBodyL | etaLams => cases EA

private theorem not_proof_at_positive_type (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort (.succ u))) (he : env.HasType univs Γ e A) : ¬ IsProof Γ e := by
  rintro ⟨P, hp, hP⟩
  have HP := (he.uniqU henv hΓ hp).of_l henv hΓ hA
  have HL := (HP.hasType.2.uniqU henv hΓ hP).sort_inv henv hΓ
  have H := congrFun HL []
  simp [VLevel.eval] at H

/-- Empty-structure eta gives two stage-zero edges through a commonly typed
original constructor, but no output stage compares the distinct variable ends.
The original unitLike equality is included, so neither erasure nor missing
intermediate typing explains the failure. -/
theorem scoped_unit_typed_composition_failure
    {Stages : Nat → List ProofShape → ProofShape → ProofShape → Prop}
    (hhead : ∀ stage {Δ a b}, Stages stage Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs Γ (VExpr.mkApps (.const family ls) ps) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (VExpr.mkApps (.const family ls) ps))
    (hjT : env.HasType univs Γ (.bvar j) (VExpr.mkApps (.const family ls) ps)) (hne : i ≠ j) :
    env.IsDefEq univs Γ (.bvar i) (.bvar j) (VExpr.mkApps (.const family ls) ps) ∧
    ∃ mid, env.HasType univs Γ mid (VExpr.mkApps (.const family ls) ps) ∧
      ScopedCompare (Stages 0) (proofEraseCtx Γ) true (proofErase Γ (.bvar i)) (proofErase Γ mid) ∧
      ScopedCompare (Stages 0) (proofEraseCtx Γ) true (proofErase Γ mid) (proofErase Γ (.bvar j)) ∧
      ∀ stage mode, ¬ ScopedCompare (Stages stage) (proofEraseCtx Γ) mode
        (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j)) := by
  have hc := hiT.unitLike_constructor henv hΓ hi hp hx hf
  have Ei : proofErase Γ (.bvar i) = .bvar i := if_neg (not_proof_at_positive_type hΓ hS hiT)
  have Ej : proofErase Γ (.bvar j) = .bvar j := if_neg (not_proof_at_positive_type hΓ hS hjT)
  have EC := proofErase_const_spine hΓ hc (not_proof_at_positive_type hΓ hS hc)
  have Hctor (m) : ScopedCompare (Stages 0) (proofEraseCtx Γ) true
      (proofErase Γ (VExpr.mkApps (.const info.ctorName ls) ps)) m := by
    rw [EC]
    have H : ScopedCompare (Stages 0) (proofEraseCtx Γ) true
        (ProofShape.mkApps (.const info.ctorName ls) (ps.map (proofErase Γ) ++ [])) m :=
      .structFields hi hx (by simpa only [List.length_map] using hp) (by simp [hf])
        (.inr (StructureReplay.ProofFields.of_no_fields hf)) (by intro i h; simp at h)
    simpa only [List.append_nil] using H
  refine ⟨IsDefEq.unitLike hi hp hx hf hiT hjT, _, hc, (Hctor _).symm, Hctor _, ?_⟩
  intro stage mode H
  rw [Ei, Ej] at H
  exact hne (H.bvar_injective (hhead stage))

/-- The typed common-intermediate counterexample persists through all actual
general singleton stages. It requires a registered non-propositional empty
structure and two variables at that family; no recursive declaration is used. -/
theorem scoped_typed_singleton_unit_composition_failure
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs Γ (VExpr.mkApps (.const family ls) ps) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (VExpr.mkApps (.const family ls) ps))
    (hjT : env.HasType univs Γ (.bvar j) (VExpr.mkApps (.const family ls) ps)) (hne : i ≠ j) :
    ∃ mid, env.HasType univs Γ mid (VExpr.mkApps (.const family ls) ps) ∧
      ScopedCompare (ErasedScopedTypedSingletonStage D 0) (proofEraseCtx Γ) true
        (proofErase Γ (.bvar i)) (proofErase Γ mid) ∧
      ScopedCompare (ErasedScopedTypedSingletonStage D 0) (proofEraseCtx Γ) true
        (proofErase Γ mid) (proofErase Γ (.bvar j)) ∧
      ∀ stage mode, ¬ ScopedCompare (ErasedScopedTypedSingletonStage D stage) (proofEraseCtx Γ) mode
        (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j)) :=
  (scoped_unit_typed_composition_failure erased_scoped_typed_singleton_stage_head
    hΓ hi hp hx hf hS hiT hjT hne).2

end Lean4Lean.VEnv.Strengthening
