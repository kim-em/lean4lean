import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedCastGuard

/-! # A cast whose target type itself needs a cast certificate

The outer cast's endpoint types are syntactically different. Its equality proof
is constructed from canonical reflexivity and checked conversion, while the
endpoint computation certificate is supplied by the inner cast guard. Stage two
is a proved upper bound; minimality of that bound is not claimed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- An actual nested cast exercises the recursive endpoint constructor.
No outer equality witness or semantic endpoint equation is assumed: both are
constructed from the inner cast. The resulting guard has finite bound two. -/
theorem nested_cast_guard
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hX : env.HasType univs Γ X (.sort u))
    (hx : env.HasType univs Γ x X)
    (hr : env.HasType univs Γ r
      (eqApp (.succ (.succ u)) (.sort (.succ u)) (.sort u) (.sort u))) :
    let Y := typeCast (.succ u) (.sort u) (.sort u) r X
    let p := eqReflApp (.succ u) (.sort u) X
    env.HasType univs Γ p (eqApp (.succ u) (.sort u) X Y) ∧
      env.HasType univs Γ (typeCast u X Y p x) Y ∧
      LevelStagedCastGuard D 2 mode (proofErase Γ (typeCast u X Y p x)) (proofErase Γ x) := by
  dsimp only
  have HI := IsDefEq.typeCast_refl henv heq (u := .succ u) (by exact hu) hΓ
    (HasType.sort hu) hr hX
  have HP := (IsDefEq.eqApp_r heq (by exact hu) (HasType.sort hu) hX HI.symm).defeq
    (HasType.eqReflApp heq (by exact hu) (HasType.sort hu) hX)
  have HC := HasType.typeCast henv.ordered heq hu hX HI.hasType.1 HP hx
  have HG : LevelCastGuard D true
      (proofErase Γ (typeCast (.succ u) (.sort u) (.sort u) r X)) (proofErase Γ X) :=
    .cast (by exact hu) hΓ (HasType.sort hu) hr hX
  exact ⟨HP, HC, .cast hu hΓ hX HI.hasType.1 HP hx HG.staged.symm⟩

omit [Params] in
/-- In an actual canonical-Eq environment the nested example retains a staged
certificate and comparison after arbitrary independent level-core computation.
The endpoint guard is built explicitly, not supplied by a coverage hypothesis. -/
theorem EnvironmentCore.nested_cast_guard_forward {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {u Γ X x r left right Δ mode}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ X (.sort u) → env.HasType U Γ x X →
      env.HasType U Γ r (eqApp (.succ (.succ u)) (.sort (.succ u)) (.sort u) (.sort u)) →
      ProofShape.Compute (ErasedLevelCore definitions)
        (proofErase Γ (typeCast u X (typeCast (.succ u) (.sort u) (.sort u) r X)
          (eqReflApp (.succ u) (.sort u) X) x)) left →
      ProofShape.Compute (ErasedLevelCore definitions) (proofErase Γ x) right →
      LevelStagedCastGuard definitions 2 mode left right ∧
        ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 2) Δ mode left right := by
  letI := henv.params U
  intro u Γ X x r left right Δ mode heq hu hΓ hX hx hr RL RR
  have H := (nested_cast_guard (D := definitions) (mode := mode) heq hu hΓ hX hx hr).2.2
  exact ⟨H.reducts RL RR, staged_cast_guard_forward henv U heq H RL RR⟩

end Lean4Lean.VEnv.Strengthening
