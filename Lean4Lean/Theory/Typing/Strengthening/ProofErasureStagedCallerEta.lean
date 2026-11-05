import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFullIdentityEtaPeak

/-! # The identity eta peak inside a caller at the first guarded stage

Standalone residuals encode an arbitrary type conversion. A caller with a
stage-zero displayed function domain repairs the observed peak at stage one
itself, without joining those domains. This distinguishes the guarded type-valued
case from the standalone-function necessity theorem. It does not preserve the
caller guard under computation or prove confluence of all type-valued forks.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Both eta expansions use guards from stage n. Nesting the fresh argument's
eta inside the caller's lambda does not require a further guard stage. The
supplied function has no recovery premise, and proof inputs are included. -/
theorem staged_caller_argument_eta
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) Δ f
      (.forallE (.forallE A B) C))
    (SQ : DomainSort Δ (.forallE A B) u) (hu : ¬ u ≈ .zero)
    (SA : DomainSort (.forallE A B :: Δ) (A.liftN 1) v) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n + 1)) Δ (.app f x)
      (.app f (.lam A (.app (x.liftN 1) (etaArgument v)))) := by
  have RF : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n + 1)) Δ f
      (.lam (.forallE A B) (.app (f.liftN 1) (.bvar 0))) := by
    have R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n + 1)) Δ f
        (.lam (.forallE A B) (.app (f.liftN 1) (etaArgument u))) :=
      .base (.inr (.inr (.inr (.inr (.inl (.intro RN SQ))))))
    simpa only [etaArgument, if_neg hu] using R
  have RX : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n)
      (.forallE A B :: Δ) (.bvar 0) (.forallE (A.liftN 1) (B.liftN 1 1)) := .bvar
  have RE : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n + 1)) (.forallE A B :: Δ)
      (.bvar 0) (.lam (A.liftN 1) (.app (.bvar 1) (etaArgument v))) := by
    simpa only [ProofShape.liftN, liftVar, Nat.not_lt_zero, ↓reduceIte] using
      (ScopedCompute.base (.inr (.inr (.inr (.inr (.inl (.intro RX SA)))))))
  apply (ScopedCompute.app RF .refl).trans
  apply (ScopedCompute.app (ScopedCompute.lam .refl (ScopedCompute.app .refl RE)) .refl).trans
  have R := ProofShape.BetaRed.beta (A := .forallE A B)
    (b := .app (f.liftN 1) (.lam (A.liftN 1) (.app (.bvar 1) (etaArgument v)))) (a := x)
  apply ScopedCompute.beta
  unfold etaArgument at R ⊢
  by_cases hv : v ≈ .zero <;> simpa only [hv, ↓reduceIte, ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
    ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.Subst.lift,
    ProofShape.lift_subst_cons, ProofShape.subst_id] using R

/-- A constant function's written domain is replaced by the caller's selected
domain in just the next stage, including the erased-proof argument case. -/
theorem staged_caller_reannotates_constant
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) Δ f
      (.forallE (.forallE A B) C))
    (SQ : DomainSort Δ (.forallE A B) u) (hu : ¬ u ≈ .zero)
    (SA : DomainSort (.forallE A B :: Δ) (A.liftN 1) v) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n + 1)) Δ
      (.app f (.lam L (.sort w))) (.app f (.lam A (.sort w))) :=
  (staged_caller_argument_eta RN SQ hu SA).trans (.beta (.app .refl (.lam .refl .beta)))

/-- Observing the explicit identity peak through a stage-zero native caller
joins both residuals at stage one. The caller chooses any displayed domain K,
not necessarily either domain in the original conversion. No domain join or
native recovery of either supplied lambda is assumed. -/
theorem first_stage_identity_eta_caller_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) f
      (.forallE (.forallE K E) C))
    (SQ : DomainSort (proofEraseCtx Γ) (.forallE K E) v) (hv : ¬ v ≈ .zero)
    (SK : DomainSort (.forallE K E :: proofEraseCtx Γ) (K.liftN 1) w) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
        (.app f (.lam (proofErase Γ A) (.sort .zero))) (.app f (.lam K (.sort .zero))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
        (.app f (identityEtaTarget Γ A B u)) (.app f (.lam K (.sort .zero))) := by
  have Rβ := (identity_eta_full_conversion_peak heq hs hΓ HAB).2.2.2.1
  exact ⟨staged_caller_reannotates_constant RN SQ hv SK,
    (ScopedCompute.beta (.app .refl Rβ)).trans (staged_caller_reannotates_constant RN SQ hv SK)⟩

/-- Every ordinarily typed type-valued caller admits this observed first-stage
peak once its assigned Pi is retained in an explicit identity wrapper. All
native and domain-sort premises are discharged. Both source branches and both
residual paths stay in stage one, even for arbitrary converted domains A and B.
The wrapper is retained during the repair; reducing it first is a different,
still-unresolved caller-history peak. -/
theorem first_stage_covered_type_caller_identity_peak
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (hf : env.HasType univs Γ f
      (.forallE (.forallE B (.sort (.succ .zero))) (.sort v))) :
    let F := VExpr.forallE (.forallE B (.sort (.succ .zero))) (.sort v)
    let caller := VExpr.app (.lam F (.bvar 0)) f
    let source := VExpr.app caller (identityEtaSource A B)
    let left := ProofShape.app (proofErase Γ caller) (.lam (proofErase Γ A) (.sort .zero))
    let right := ProofShape.app (proofErase Γ caller) (identityEtaTarget Γ A B u)
    let shared := ProofShape.app (proofErase Γ caller) (.lam (proofErase Γ B) (.sort .zero))
    env.HasType univs Γ source (.sort v) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
        (proofErase Γ source) left ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
        (proofErase Γ source) right ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) left shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) right shared := by
  dsimp only
  let Q := VExpr.forallE B (.sort (.succ .zero))
  let F := VExpr.forallE Q (.sort v)
  let caller := VExpr.app (.lam F (.bvar 0)) f
  have hB := HAB.hasType.2
  have hQ : env.HasType univs Γ Q (.sort (.imax u (.succ (.succ .zero)))) :=
    .forallE hB (.sort (by trivial))
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, hB⟩
  have hΓQ : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have EQ : proofErase Γ Q = .forallE (proofErase Γ B) (.sort (.succ .zero)) := by
    rw [show proofErase Γ Q = .forallE (proofErase Γ B) (proofErase (B :: Γ) (.sort (.succ .zero))) from
      if_neg (not_isProof_of_sort hΓ hQ)]
    exact congrArg (ProofShape.forallE (proofErase Γ B))
      (if_neg (not_isProof_of_sort hΓB (HasType.sort (by trivial))))
  obtain ⟨_, hF⟩ := hf.isType henv hΓ
  obtain ⟨_, _, hC⟩ := hF.forallE_inv henv
  have EF : proofErase Γ F = .forallE (proofErase Γ Q) (.sort v) := by
    rw [show proofErase Γ F = .forallE (proofErase Γ Q) (proofErase (Q :: Γ) (.sort v)) from
      if_neg (not_isProof_of_sort hΓ hF)]
    exact congrArg (ProofShape.forallE (proofErase Γ Q))
      (if_neg (not_isProof_of_sort hΓQ hC))
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ caller) (.forallE (.forallE (proofErase Γ B) (.sort (.succ .zero))) (.sort v)) := by
    have R : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ caller) (proofErase Γ F) :=
      proofErase_identity_wrapper_native hΓ hf (not_isProof_function_to_sort hΓ hf)
    simpa only [EF, EQ] using R
  have SQ : DomainSort (proofEraseCtx Γ) (.forallE (proofErase Γ B) (.sort (.succ .zero)))
      (.imax u (.succ (.succ .zero))) := EQ ▸ DomainSort.of_typed hΓ hQ
  have hpos : ¬ VLevel.imax u (.succ (.succ .zero)) ≈ .zero := by
    intro H
    rw [VLevel.equiv_def] at H
    have H0 := H []
    simp [VLevel.eval, Lean.Nat.imax] at H0
  have SB : DomainSort (.forallE (proofErase Γ B) (.sort (.succ .zero)) :: proofEraseCtx Γ)
      ((proofErase Γ B).liftN 1) u := by
    have R := DomainSort.of_typed hΓQ (hB.weakN henv Ctx.LiftN.one)
    simpa only [proofEraseCtx, EQ, proofErase_liftN hΓ hΓQ Ctx.LiftN.one hB] using R
  obtain ⟨hx, RB, RE, _⟩ := identity_eta_full_conversion_peak heq hs hΓ HAB
  have hc : env.HasType univs Γ caller F := (nativeIdentityExpansion_equal hf).hasType.1
  have ht : env.HasType univs Γ (.app caller (identityEtaSource A B)) (.sort v) := .app hc hx
  have Es : proofErase Γ (.app caller (identityEtaSource A B)) =
      .app (proofErase Γ caller) (proofErase Γ (identityEtaSource A B)) :=
    if_neg (not_isProof_of_sort hΓ ht)
  obtain ⟨RL, RR⟩ := first_stage_identity_eta_caller_join heq hs hΓ HAB RN SQ hpos SB
  refine ⟨ht, ?_, ?_, RL, RR⟩
  · rw [Es]
    exact .beta (.app .refl RB)
  · rw [Es]
    exact .app .refl (.base (.inr (.inr (.inr (.inr (.inl RE))))))

end Lean4Lean.VEnv.Strengthening
