import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutHistoryNativePivot
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeBetaPrimitiveResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaDomainObservation

/-! # Primitive residuals after historical cut components have evolved

A later native guard is used at an earlier recoverable pivot, then argument
computation follows inside its output. This closes primitive competitors of a
historical marked cut without asserting native recovery of its current argument
or exact recovery across its current beta contraction.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private empty_compute_beta from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedComparison
variable [Params] {D : PureObservation.Definitions}

/-- A typed raw binder permits weakening a full-union path. No native recovery
of its source or target is required; interpreted renaming preserves each guard. -/
theorem static_structure_compute_under_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (SD : DomainSort Δ A u)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a b) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (A :: Δ) (a.liftN 1) (b.liftN 1) := by
  obtain ⟨Γ, A₀, hΓ, rfl, hA, rfl⟩ := SD
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hrename : ∀ {Δ Δ' a b τ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' τ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst τ) (b.subst τ) := by
    intro Δ Δ' a b τ ⟨stage, H⟩ W
    exact ⟨stage, erased_static_structure_eta_expansion_stage_rename heq hs stage H W⟩
  simpa only [subst_bvar_liftN, proofEraseCtx] using
    R.rename hrename (ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one)

/-- A primitive at the evolved cut joins contraction of the original cut.
Native eta and structure expansion use the historical pivot, so no certificate
of the current contraction is assumed. The primitive branch needs only beta
to reach the shared output; the other branch may use full-union computation. -/
theorem CutComponentHistory.primitive_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutComponentHistory D Γ A b x u B s)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RP : ErasedStaticStructureEtaExpansionUnion D (proofEraseCtx Γ) s.redex expanded) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧ ProofShape.BetaRed expanded shared := by
  have Rβ : ProofShape.BetaRed s.redex (s.2.1.inst s.2.2) := .beta
  rcases static_structure_beta_redex_primitive RP with RC | RI | RE | RS
  · cases RC
    exact ⟨_, (H.contract heq hs hΓ HR).1, (constantExpansion_beta _).trans Rβ⟩
  · cases RI with
    | intro _RN =>
      rename_i annotation
      have RIβ : ProofShape.BetaRed (.app (.lam annotation (.bvar 0)) s.redex) s.redex := by
        simpa only [ProofShape.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
          ProofShape.liftN_zero] using (ProofShape.BetaRed.beta (b := .bvar 0) (a := s.redex))
      exact ⟨_, (H.contract heq hs hΓ HR).1, RIβ.trans Rβ⟩
  · cases RE with
    | intro RN SD =>
      obtain ⟨pivot, _, Rbefore, Rafter, RNpivot⟩ := H.native_pivot heq hs hΓ hn HR RN
      have RL := static_structure_compute_under_domain heq hs SD Rafter
      exact ⟨_, Rbefore.trans ((ScopedCompute.base
          (erased_static_structure_eta_expansion_union_eta (.intro RNpivot SD))).trans
            (.lam .refl (.app RL .refl))),
        .lam .refl (.app Rβ.liftN .refl)⟩
  · cases RS with
    | intro hi hx ha hp RN =>
      obtain ⟨pivot, _, Rbefore, Rafter, RNpivot⟩ := H.native_pivot heq hs hΓ hn HR RN
      refine ⟨_, Rbefore.trans ((ScopedCompute.base
        (erased_static_structure_eta_expansion_union_structure (.intro hi hx ha hp RNpivot))).trans
          (nativeStructureOutput_compute (List.Forall₂.rfl (fun _ _ => ScopedCompute.refl)) Rafter)), ?_⟩
      apply empty_compute_beta
      exact (nativeStructureOutput_compute (List.Forall₂.rfl (fun _ _ => ScopedCompute.refl))
        (ScopedCompute.beta (Step := fun _ _ _ => False) (Δ := proofEraseCtx Γ) Rβ)).core_forget

end Lean4Lean.VEnv.Strengthening
