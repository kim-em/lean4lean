import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin

/-! # A caller can change its retained function argument's annotation

Eta first exposes the caller's declared argument type. Eta on that newly bound
function uses its declared domain, and beta then supplies the original argument.
Neither step requires a native certificate for the supplied argument itself.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private ProofShape.liftN_app_inv ProofShape.liftN_lam_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
variable [Params]

/-- Two eta expansions in the caller, followed by beta, eta-expand its
argument at the caller's selected domain. Native recovery of that argument at
the selected domain is not a premise. -/
theorem static_structure_caller_argument_eta
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ f
      (.forallE (.forallE A B) C))
    (SQ : DomainSort Δ (.forallE A B) u) (hu : ¬ u ≈ .zero)
    (SA : DomainSort (.forallE A B :: Δ) (A.liftN 1) v) (hv : ¬ v ≈ .zero) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ (.app f x)
      (.app f (.lam A (.app (x.liftN 1) (.bvar 0)))) := by
  have RF : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ f
      (.lam (.forallE A B) (.app (f.liftN 1) (.bvar 0))) := by
    simpa only [etaArgument, if_neg hu] using
      (ScopedCompute.base (erased_static_structure_eta_expansion_union_eta (.intro RN SQ)))
  have RX : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (.forallE A B :: Δ) (.bvar 0) (.forallE (A.liftN 1) (B.liftN 1 1)) := .bvar
  have RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (.forallE A B :: Δ)
      (.bvar 0) (.lam (A.liftN 1) (.app (.bvar 1) (.bvar 0))) := by
    simpa only [etaArgument, if_neg hv, ProofShape.liftN, liftVar, Nat.not_lt_zero, ↓reduceIte] using
      (ScopedCompute.base (erased_static_structure_eta_expansion_union_eta (.intro RX SA)))
  apply (ScopedCompute.app RF .refl).trans
  apply (ScopedCompute.app (ScopedCompute.lam .refl (ScopedCompute.app .refl RE)) .refl).trans
  apply ScopedCompute.beta
  have R := BetaRed.beta (A := .forallE A B)
    (b := .app (f.liftN 1) (.lam (A.liftN 1) (.app (.bvar 1) (.bvar 0)))) (a := x)
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
    ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.Subst.lift,
    ProofShape.lift_subst_cons, ProofShape.subst_id] using R

/-- A constant function argument can acquire the caller's selected domain
as its literal annotation. The resulting argument need not be a computation
of the old argument in isolation. -/
theorem static_structure_caller_reannotates_constant
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ f
      (.forallE (.forallE A B) C))
    (SQ : DomainSort Δ (.forallE A B) u) (hu : ¬ u ≈ .zero)
    (SA : DomainSort (.forallE A B :: Δ) (A.liftN 1) v) (hv : ¬ v ≈ .zero) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ (.app f (.lam L (.sort w)))
      (.app f (.lam A (.sort w))) := by
  apply (static_structure_caller_argument_eta (x := .lam L (.sort w)) RN SQ hu SA hv).trans
  apply ScopedCompute.beta
  apply ProofShape.BetaRed.app .refl
  apply ProofShape.BetaRed.lam .refl
  exact .beta

/-- No descending computation can introduce a freshly inserted variable in
a retained argument inside a lambda annotation when its source was typed below
the insertion. This applies even if the final lambda is well typed above it. -/
theorem compute_no_inserted_lambda_domain_argument
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T)
    (hj : k ≤ j) (hj' : j < k+n) :
    ¬ ScopedCompute Step (proofEraseCtx Γ') ((proofErase Γ e).liftN n k)
      (.lam (.app f (.bvar j)) b) := by
  intro R
  obtain ⟨e', _, EE⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ' W ht rfl R
  obtain ⟨A, _, _, EA, _⟩ := ProofShape.liftN_lam_inv EE
  obtain ⟨_, a, _, _, Ea⟩ := ProofShape.liftN_app_inv EA
  cases a <;> simp only [ProofShape.liftN] at Ea <;> try cases Ea
  simp only [liftVar] at hj hj'
  split at hj <;> simp_all <;> omega

end Lean4Lean.VEnv.Strengthening
