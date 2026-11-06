import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedCastGuard

/-! # Created head beta after certified cast removal

The lambda body and its argument are unrestricted. Their instantiated body
keeps a reusable staged certificate against the cast application, so further
core computation on either side is already covered by the guard induction.
This handles explicit certified casts in function position; arbitrary semantic
conversion of written lambda annotations remains outside the certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Removing a certified function cast and contracting the newly exposed beta
redex retains a recursive certificate. There is no normalization, atomicity or
recovery condition on the argument, and no comparison premise on the contractum. -/
theorem LevelStagedCastGuard.cast_beta
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ (.forallE A B) (.sort u))
    (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) (.forallE A B) Y))
    (hf : env.HasType univs Γ (.lam A b) (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (ht : env.HasType univs Γ (.app (typeCast u (.forallE A B) Y q (.lam A b)) x) T)
    (H : LevelStagedCastGuard D n true (proofErase Γ (.forallE A B)) (proofErase Γ Y)) :
    LevelStagedCastGuard D (n+1) mode
      (proofErase Γ (.app (typeCast u (.forallE A B) Y q (.lam A b)) x))
      (proofErase Γ (b.inst x)) :=
  .reducts (.castSpine (args := [x]) hu hΓ hX hY hq hf ht H) .refl
    (.beta (proofErase_beta_forward hΓ (HasType.app hf hx) .beta))

omit [Params] in
/-- Actual canonical-Eq environments support the created-beta certificate
after independent arbitrary full-core computation of the cast application and
its contractum, at one stage above the endpoint certificate's finite bound. -/
theorem EnvironmentCore.staged_cast_beta_forward {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {u Γ A B Y q b x T n mode left right Δ}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ (.forallE A B) (.sort u) →
      env.HasType U Γ Y (.sort u) →
      env.HasType U Γ q (eqApp (.succ u) (.sort u) (.forallE A B) Y) →
      env.HasType U Γ (.lam A b) (.forallE A B) → env.HasType U Γ x A →
      env.HasType U Γ (.app (typeCast u (.forallE A B) Y q (.lam A b)) x) T →
      LevelStagedCastGuard definitions n true (proofErase Γ (.forallE A B)) (proofErase Γ Y) →
      ProofShape.Compute (ErasedLevelCore definitions)
        (proofErase Γ (.app (typeCast u (.forallE A B) Y q (.lam A b)) x)) left →
      ProofShape.Compute (ErasedLevelCore definitions) (proofErase Γ (b.inst x)) right →
      LevelStagedCastGuard definitions (n+1) mode left right ∧
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions (n+1)) Δ mode left right := by
  letI := henv.params U
  intro u Γ A B Y q b x T n mode left right Δ heq hu hΓ hX hY hq hf hx ht H RL RR
  have HG := H.cast_beta (mode := mode) hu hΓ hX hY hq hf hx ht
  exact ⟨HG.reducts RL RR, staged_cast_guard_forward henv U heq HG RL RR⟩

end Lean4Lean.VEnv.Strengthening
