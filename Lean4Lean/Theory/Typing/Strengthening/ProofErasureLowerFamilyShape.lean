import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLowerTypeHistory

/-! # Family-head constraints on historical types under temporary binders -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- A lower type history with a typed original source has an ordinary
realization at every temporary prefix. This uses forward realization and
weakening, not strengthening of a new equality or recovery of an argument. -/
theorem LowerTypeHistory.realize_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (H : LowerTypeHistory D Γ (proofErase Γ A) n Δ out)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ') :
    ∃ B, env.IsDefEq univs Γ' (A.liftN n) B (.sort u) ∧ proofErase Γ' B = out := by
  obtain ⟨C, _, _, _, EC, _, R⟩ := H
  obtain ⟨B, HE, EB⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hA rfl rfl R
  refine ⟨B.liftN n, HE.weakN henv W, ?_⟩
  rw [proofErase_liftN hΓ hΓ' W HE.hasType.2, EB]
  exact EC

/-- A historical rigid-family type cannot become a literal Pi, even beneath
temporary control binders and after arbitrary native conversion histories. -/
theorem LowerTypeHistory.family_not_pi
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hr : env.Rigid r)
    (hA : env.HasType univs Γ (VExpr.mkApps (.const r []) args) (.sort u))
    (H : LowerTypeHistory D Γ (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ (.forallE X Y))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ') : False := by
  obtain ⟨B, HE, EB⟩ := H.realize_origin heq hs hΓ hA hΓ' W
  obtain ⟨X', Y', rfl, _, _, _⟩ := erase_forallE_inv EB
  simp only [VExpr.liftN_mkApps, VExpr.liftN] at HE
  exact henv.headInversion.forallE_rigid hΓ' hr (HE.symm.toU.typeChain henv hΓ' HE.hasType.2)

/-- A registered family selected by a historical monomorphic family type
has the original head and empty universe instance. Its parameter values may
have changed; their ancestry stays in the historical ground certificate. -/
theorem LowerTypeHistory.family_shape
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hr : env.Rigid r)
    (hA : env.HasType univs Γ (VExpr.mkApps (.const r []) args) (.sort u))
    (hi' : env.projections r' info')
    (H : LowerTypeHistory D Γ (proofErase Γ (VExpr.mkApps (.const r []) args)) n Δ
      (ProofShape.mkApps (.const r' ls) ps))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ') : r = r' ∧ ls = [] := by
  obtain ⟨B, HE, EB⟩ := H.realize_origin heq hs hΓ hA hΓ' W
  obtain ⟨bs, rfl, _⟩ := proofErase_const_spine_inv EB
  simp only [VExpr.liftN_mkApps, VExpr.liftN] at HE
  obtain ⟨E, HL, _⟩ := henv.headInversion.rigid_rigid hΓ' hr (henv.projectionRigid hi')
    (HE.toU.typeChain henv hΓ' HE.hasType.1)
  cases HL
  exact ⟨E, rfl⟩

end Lean4Lean.VEnv.Strengthening
