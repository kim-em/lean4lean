import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureRecord

/-! # A two-field dependent record test

For a registered record with constructor (A : Type) → A → Pack, the second
field's carrier is the first projection of the left major. The future record
construction tracks that projection through substitutions and independent
major beta paths. Registration is assumed explicitly, not synthesized here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem dependent_recipes
    (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (HT : ProjTele env univs family info [] doms result) :
    projectionType family info doms 0 (by have := HT.numFields; omega) [] major = .sort (.succ .zero) ∧
    projectionType family info doms 1 (by have := HT.numFields; omega) [] major = .proj family 0 major := by
  have hlen : doms.length = 2 := by have := HT.numFields; omega
  cases doms with
  | nil => cases hlen
  | cons A ds =>
    cases ds with
    | nil => cases hlen
    | cons B ds =>
      have hnil : ds = [] := by simpa using hlen
      subst ds
      have HE := hshape.symm.trans HT.shape
      change VExpr.forallE _ _ = .forallE A (.forallE B result) at HE
      have HA := (VExpr.forallE.inj HE).1
      have HB := (VExpr.forallE.inj (VExpr.forallE.inj HE).2).1
      subst A
      subst B
      have hC : OnCtx [VExpr.sort (.succ .zero)] (env.IsType univs) :=
        ⟨trivial, _, HasType.sort (by trivial)⟩
      have hv : env.HasType univs [VExpr.sort (.succ .zero)] (.bvar 0) (.sort (.succ .zero)) := .bvar .zero
      have EV : proofErase [VExpr.sort (.succ .zero)] (.bvar 0) = .bvar 0 :=
        if_neg (not_isProof_of_sort hC hv)
      have ES : proofErase [] (.sort (.succ .zero)) = .sort (.succ .zero) :=
        if_neg (not_isProof_of_sort (by trivial) (HasType.sort (by trivial)))
      simp [projectionType, projectionArgs, hp, EV, ES, ProofShape.instOuter,
        ProofShape.subst, ProofShape.Subst.ofList]

/-- The future guard for a dependent two-field record uses common comparison
of its type fields and carrier checking of its values at the first projection
of the left major. The carrier depends on an earlier field, not only parameters.
Every future major reduction and substitution updates that dependency. -/
theorem BetaStableCarrier.dependent_pair
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hadm : (info.resultLevel.inst []).IsNeverZero)
    (HTy : BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ (.proj family 0 a) (.proj family 0 b))
    (HVal : BetaStableCarrier Step Δ (.proj family 0 a) (.proj family 1 a) (.proj family 1 b)) :
    BetaStableCarrier Step Δ (.const family []) a b := by
  obtain ⟨doms, result, HT⟩ := projection_telescope_exists (ls := []) hi (by simp)
  apply BetaStableCarrier.record_nested hi hx (ps := []) hp.symm (.inl hadm) HT
  intro i hj hn
  obtain ⟨E₀, E₁⟩ := dependent_recipes (major := a) hp hf hshape HT
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · rw [E₀]
    exact HTy.carrier
  · rw [E₁]
    exact HVal

end Lean4Lean.VEnv.Strengthening
