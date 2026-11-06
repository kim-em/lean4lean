import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralEtaCoreComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralEtaChecking

/-! # Comparing neutral eta consumers after full core computation

Native recovery expands the protected variable at one later stage. Arbitrary
ordinary core paths in its domain retain that expansion, and primitive
simulation preserves the eta marks throughout independently reduced consumers.
Actual literal lookup supplies the initial recovery at stage zero.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A full core history of the written domain follows the native expansion
at the same successor stage. The domain need not normalize. -/
theorem neutral_eta_native_core_residual_expansion
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage) Δ (.bvar i) (.forallE A B))
    (SA : DomainSort Δ A u) (hu : ¬ u ≈ .zero) (R : Compute (ErasedLevelCore D) A C) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D (stage+1)) Δ (.bvar i)
      (.lam C (.app (.bvar (i+1)) (.bvar 0))) :=
  (neutral_eta_native_residual_expansion RN SA hu .refl).trans (.lam R.in_static_stage .refl)

/-- Independent full core residuals of every typed neutral eta consumer
compare at one fixed stage. Native Pi recovery remains explicit; the paths
include recursive delta, projection, quotient, stored iota and universe steps. -/
theorem proofErase_neutral_eta_consumer_core_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (.bvar i) (.forallE A B))
    (hn : ¬ IsProof Γ (.bvar i)) (hu : ¬ u ≈ .zero)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage)
      (proofEraseCtx Γ) (.bvar i) (.forallE (proofErase Γ A) rawB))
    (RL : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.bvar i))) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
      (proofEraseCtx Γ) mode left right := by
  have V : NeutralEtaVariant (fun C j => j = i ∧ Compute (ErasedLevelCore D) (proofErase Γ A) C) 0
      (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0)))))
      (proofErase Γ (t.inst (.bvar i))) :=
    (proofErase_neutral_eta_consumer_variant hΓ hA hf hn hu ht).guard_mono
      (fun H => ⟨H.1, .beta H.2⟩)
  obtain ⟨left', right', PL, PR, V⟩ := neutral_eta_level_core_residuals hc
    (fun H R => ⟨H.1, H.2.trans R⟩) hΓ (ht.instN henv Ctx.InstN.zero hf) V RL RR
  have hleft := ht.instN henv Ctx.InstN.zero (IsDefEq.eta hf).hasType.1
  obtain ⟨e, HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hleft rfl rfl ((RL.trans PL).scoped (fun H => .base H))
  have HG {C j} (H : j = i ∧ Compute (ErasedLevelCore D) (proofErase Γ A) C) :
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D (stage+1)) (proofEraseCtx Γ)
        (.bvar j) (.lam C (.app (.bvar (j+1)) (.bvar 0))) := by
    obtain ⟨rfl, R⟩ := H
    exact neutral_eta_native_core_residual_expansion RN (.of_typed hΓ hA) hu R
  have HC := neutral_eta_variant_computed_check (mode := mode)
    (erased_static_structure_eta_expansion_stage_rename heq hs (stage+1)) (fun H => HG H)
    V hΓ HE.hasType.2 EE ContextRenaming.identity
  exact .compute PL.in_static_stage PR.in_static_stage HC

/-- Literal context lookup discharges native Pi recovery. Every pair of full
core residuals of its typed eta consumer compares at stage one, with no
normalization, head-exposure or separate recovery premise. -/
theorem proofErase_lookup_eta_consumer_core_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (HL : Lookup Γ i (.forallE A B))
    (hn : ¬ IsProof Γ (.bvar i)) (hu : ¬ u ≈ .zero)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RL : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.bvar i))) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 1)
      (proofEraseCtx Γ) mode left right := by
  have hf : env.HasType univs Γ (.bvar i) (.forallE A B) := .bvar HL
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  have EF : proofErase Γ (.bvar i) = .bvar i := if_neg hn
  have EP : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  have RN := proofErase_scoped_lookup_recovery
    (Step := ErasedStaticStructureEtaExpansionStage D 0) hΓ HL hn .refl
  rw [EF, EP] at RN
  exact proofErase_neutral_eta_consumer_core_compare heq hs hc hΓ hA hf hn hu ht RN RL RR

omit [Params] in
/-- An actual well-formed canonical-Eq environment supplies core soundness
and typed confluence. All ordinary core tails of the native neutral eta
consumer are covered, including recursive definitions and created redexes. -/
theorem EnvironmentCore.lookup_eta_consumer_core_compare
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {mode Γ A B i u t T left right}, env.HasCanonicalEq →
      OnCtx Γ (env.IsType U) → env.HasType U Γ A (.sort u) →
      Lookup Γ i (.forallE A B) → (¬ IsProof Γ (.bvar i)) → (¬ u ≈ .zero) →
      env.HasType U (.forallE A B :: Γ) t T →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0))))) left →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.bvar i))) right →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 1)
        (proofEraseCtx Γ) mode left right := by
  letI := henv.params U
  intro mode Γ A B i u t T left right heq hΓ hA HL hn hu ht RL RR
  exact proofErase_lookup_eta_consumer_core_compare heq sound
    (typed_level_core_confluence (fun H => H)) hΓ hA HL hn hu ht RL RR

end Lean4Lean.VEnv.Strengthening
