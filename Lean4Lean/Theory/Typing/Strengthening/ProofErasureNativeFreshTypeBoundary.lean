import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBetaRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitEtaNativeRepair

/-! # Exact assigned-type recovery is incompatible with binder descent

A source already typed below an unused binder cannot natively recover a raw
type mentioning that binder in a retained position. Unit equality can still
assign it such a type. This excludes universal exact recovery for every
primitive relation with descent, not merely the present eta grammar.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private ProofShape.liftN_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- A native type recovered above insertion cannot contain a fresh binder as
a retained application argument when its source was typed below insertion. -/
theorem native_recovery_no_inserted_argument
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T)
    (hj : k ≤ j) (hj' : j < k+n) :
    ¬ ScopedTypeRecovery Step (proofEraseCtx Γ') (proofErase Γ' (e.liftN n k)) (.app f (.bvar j)) := by
  intro R
  rw [proofErase_liftN hΓ hΓ' W ht] at R
  obtain ⟨A, _, EA⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ' W ht rfl R
  obtain ⟨_, a, _, _, Ea⟩ := ProofShape.liftN_app_inv EA
  cases a <;> simp only [ProofShape.liftN] at Ea <;> try cases Ea
  simp only [liftVar] at hj hj'
  split at hj <;> simp_all <;> omega

/-- A closed positive empty structure supplies an actually assigned type that
no descending native-recovery language can recover exactly. The same source
already has a type below the unused unit binder. No canonical Eq assumption is
needed for this obstruction to exact coverage. -/
theorem descending_native_exact_coverage_failure
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ p A, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ p A ∧ ¬ IsProof Γ p ∧
      (¬ ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A)) ∧
      ∀ D : PureObservation.Definitions, ∃ shared,
        ScopedTypeRecovery (ErasedUnitEtaExpansionStage D 1) (proofEraseCtx Γ) (proofErase Γ p) shared ∧
        ScopedCompute (ErasedUnitEtaExpansionStage D 1) (proofEraseCtx Γ) (proofErase Γ A) shared := by
  let S := VExpr.const family []
  let FT := VExpr.forallE S (.sort (.succ .zero))
  have hFT : env.HasType univs [] FT (.sort (.imax (.succ u) (.succ (.succ .zero)))) :=
    .forallE hS (.sort (by trivial))
  let Γ₀ := [FT, S]
  have hΓ₀ : OnCtx Γ₀ (env.IsType univs) := ⟨⟨trivial, _, hS⟩, _, hFT.weak0 henv.ordered⟩
  have hF₀ : env.HasType univs Γ₀ (.bvar 0) FT := .bvar .zero
  have hI₀ : env.HasType univs Γ₀ (.bvar 1) S := .bvar (.succ .zero)
  have hA₀ : env.HasType univs Γ₀ (.app (.bvar 0) (.bvar 1)) (.sort (.succ .zero)) := .app hF₀ hI₀
  let Γ := .app (.bvar 0) (.bvar 1) :: Γ₀
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨hΓ₀, _, hA₀⟩
  have hp₀ : env.HasType univs Γ (.bvar 0) (.app (.bvar 1) (.bvar 2)) := .bvar .zero
  let Γ' := [.app (.bvar 0) (.bvar 1), FT, S, S]
  have W : Ctx.LiftN 1 3 Γ Γ' := (Ctx.LiftN.one (Γ := []) (A := S)).succ.succ.succ
  have hΓ₀' : OnCtx [FT, S, S] (env.IsType univs) :=
    ⟨⟨⟨trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩, _, hFT.weak0 henv.ordered⟩
  have hF₀' : env.HasType univs [FT, S, S] (.bvar 0) FT := .bvar .zero
  have hI₀' : env.HasType univs [FT, S, S] (.bvar 1) S := .bvar (.succ .zero)
  have hΓ' : OnCtx Γ' (env.IsType univs) := ⟨hΓ₀', _, HasType.app hF₀' hI₀'⟩
  have hF : env.HasType univs Γ' (.bvar 1) FT := .bvar (.succ .zero)
  have hI : env.HasType univs Γ' (.bvar 2) S := .bvar (.succ (.succ .zero))
  have hJ : env.HasType univs Γ' (.bvar 3) S := .bvar (.succ (.succ (.succ .zero)))
  have hFi : env.HasType univs Γ' (.app (.bvar 1) (.bvar 2)) (.sort (.succ .zero)) := .app hF hI
  have hFj : env.HasType univs Γ' (.app (.bvar 1) (.bvar 3)) (.sort (.succ .zero)) := .app hF hJ
  have hP : env.HasType univs Γ' (.bvar 0) (.app (.bvar 1) (.bvar 2)) := .bvar .zero
  have HE := IsDefEq.appDF hF (IsDefEq.unitLike hi (params := []) hp.symm hx hz hI hJ)
  have hn := not_proof_at_positive_type hΓ' hFi hP
  refine ⟨Γ', .bvar 0, .app (.bvar 1) (.bvar 3), hΓ', HE.defeq hP, hn, ?_, ?_⟩
  · have EJ : proofErase Γ' (.bvar 3) = .bvar 3 :=
      if_neg (not_proof_at_positive_type hΓ' (hS.weak0 henv.ordered) hJ)
    rw [show proofErase Γ' (.app (.bvar 1) (.bvar 3)) = .app _ _ from if_neg (not_isProof_of_sort hΓ' hFj), EJ]
    exact native_recovery_no_inserted_argument hstep hΓ hΓ' W hp₀ (by decide) (by decide)

  · intro D
    obtain ⟨RN, RC⟩ := unit_eta_family_native_repair (D := D) hi hp hx hz hS hΓ' hF
      (show Lookup Γ' 2 S from .succ (.succ .zero))
      (show Lookup Γ' 3 S from .succ (.succ (.succ .zero)))
      (show Lookup Γ' 0 (.app (.bvar 1) (.bvar 2)) from .zero)
    exact ⟨_, RN, RC⟩

/-- Even the full structure/function-eta language loses exact native coverage
under one identity beta contraction. Its unit repair supplies common coverage,
so exact source stability cannot be the universal invariant for this route. -/
theorem static_structure_beta_loses_exact_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ p A, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ p A ∧ ¬ IsProof Γ p ∧
      env.IsDefEq univs Γ (.app (.lam A (.bvar 0)) p) p A ∧
      ProofShape.BetaRed (proofErase Γ (.app (.lam A (.bvar 0)) p)) (proofErase Γ p) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A (.bvar 0)) p)) (proofErase Γ A) ∧
      (¬ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ p) (proofErase Γ A)) ∧
      ∃ shared, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
          (proofErase Γ p) shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) (proofErase Γ A) shared := by
  obtain ⟨Γ, p, A, hΓ, ht, hn, Hno, Hcommon⟩ := descending_native_exact_coverage_failure
    (erased_static_structure_eta_expansion_union_descent heq hs) hi hp hx hz hS
  obtain ⟨shared, RN, RC⟩ := Hcommon D
  exact ⟨Γ, p, A, hΓ, ht, hn, nativeIdentityExpansion_equal ht,
    proofErase_identity_wrapper_beta hΓ ht hn, proofErase_identity_wrapper_native hΓ ht hn, Hno,
    shared, RN.mono (erased_unit_into_static_structure_eta_stage 1),
    RC.mono (erased_unit_into_static_structure_eta_stage 1)⟩

end Lean4Lean.VEnv.Strengthening
