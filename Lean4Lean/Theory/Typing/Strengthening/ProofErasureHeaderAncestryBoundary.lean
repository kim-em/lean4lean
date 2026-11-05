import Lean4Lean.Theory.Typing.Strengthening.ProofErasureObservedDeclarationHeaders
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFreshTypeBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrapperPivotTransport

/-! # Forward header simplification does not give reverse result ancestry

A context-declared function ignores one ordinary field. Its original result
contains a fresh unit index; simplifying that index gives a result typed before
the index was inserted. Native recovery still selects the original result.
No descending computation of the simplified result can introduce that index.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private ProofShape.liftN_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params] {D : PureObservation.Definitions}

private theorem no_inserted_argument
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T)
    (hj : k ≤ j) (hj' : j < k+n) :
    ¬ ScopedCompute Step (proofEraseCtx Γ') ((proofErase Γ e).liftN n k)
      (.app f (.bvar j)) := by
  intro R
  obtain ⟨e', _, EE⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ' W ht rfl R
  obtain ⟨_, a, _, _, Ea⟩ := ProofShape.liftN_app_inv EE
  cases a <;> simp only [ProofShape.liftN] at Ea <;> try cases Ea
  simp only [liftVar] at hj hj'
  split at hj <;> simp_all <;> omega

/-- Exact native-result ancestry cannot use ordinary header equality, or even
a forward computation from the original header to the chosen field telescope.
The field telescope has one unused Type argument and an explicit Prop value.
Both headers type the same context-declared function. Its native application
selects the old result, which computes to the chosen result but cannot be reached
from it in any descending primitive language. Thus a join remains available;
this refutes reverse exact ancestry, not strengthening or common coverage.
The head is a context declaration, not a closed constant declaration. -/
theorem static_structure_forward_header_exact_ancestry_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hix : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ B C, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ B (.sort (.succ .zero)) ∧
      env.HasType univs Γ C (.sort (.succ .zero)) ∧
      env.HasType univs Γ (.bvar 0) (.forallE (.sort (.succ .zero)) B.lift) ∧
      env.HasType univs Γ (.bvar 0) (.forallE (.sort (.succ .zero)) C.lift) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.forallE (.sort (.succ .zero)) B.lift))
        (proofErase Γ (.forallE (.sort (.succ .zero)) C.lift)) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ (.app (.bvar 0) (.sort .zero))) (proofErase Γ B) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ B) (proofErase Γ C) ∧
      (∀ Step, ErasedScopedPrimitiveDescent Step →
        ¬ ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ C) (proofErase Γ B)) := by
  let S := VExpr.const family []
  let FT := VExpr.forallE S (.sort (.succ .zero))
  have hFT : env.HasType univs [] FT (.sort (.imax (.succ u) (.succ (.succ .zero)))) :=
    .forallE hS (.sort (by trivial))
  let Γ₀ := [FT, S]
  have hΓ₀ : OnCtx Γ₀ (env.IsType univs) := ⟨⟨trivial, _, hS⟩, _, hFT.weak0 henv.ordered⟩
  have hF₀ : env.HasType univs Γ₀ (.bvar 0) FT := .bvar .zero
  have hy₀ : env.HasType univs Γ₀ (.bvar 1) S := .bvar (.succ .zero)
  have hB₀ : env.HasType univs Γ₀ (.app (.bvar 0) (.bvar 1)) (.sort (.succ .zero)) := .app hF₀ hy₀
  have ES₀ : proofErase Γ₀ S = .const family [] :=
    if_neg (not_isProof_of_sort hΓ₀ (hS.weak0 henv.ordered))
  have RY := proofErase_scoped_lookup_recovery (Step := ErasedUnitEtaExpansionStage D 0)
    hΓ₀ (show Lookup Γ₀ 1 S from .succ .zero)
    (not_proof_at_positive_type hΓ₀ (hS.weak0 henv.ordered) hy₀) .refl
  rw [ES₀] at RY
  have RY' := (unit_eta_native_join hi hix hz (ps := []) hp.symm RY RY).1
  have EF₀ : proofErase Γ₀ (.bvar 0) = .bvar 0 :=
    if_neg (not_isProof_function_to_sort hΓ₀ hF₀)
  have RB₀ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (.app (.bvar 0) (.bvar 1))) (.app (.bvar 0) (.const info.ctorName [])) := by
    rw [show proofErase Γ₀ (.app (.bvar 0) (.bvar 1)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ₀ hB₀), ← EF₀]
    exact .app .refl (RY'.mono (fun H => ⟨1, erased_unit_into_static_structure_eta_stage 1 H⟩))
  obtain ⟨C₀, HC₀, EC₀⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ₀ hB₀ rfl rfl RB₀
  let Δ := S :: Γ₀
  have hΔ : OnCtx Δ (env.IsType univs) := ⟨hΓ₀, _, hS.weak0 henv.ordered⟩
  let BΔ := VExpr.app (.bvar 1) (.bvar 0)
  have hBΔ : env.HasType univs Δ BΔ (.sort (.succ .zero)) :=
    .app (show env.HasType univs Δ (.bvar 1) FT from .bvar (.succ .zero)) (.bvar .zero)
  let Q := VExpr.forallE (.sort (.succ .zero)) BΔ.lift
  have hQ : env.HasType univs Δ Q (.sort (.imax (.succ (.succ .zero)) (.succ .zero))) :=
    .forallE (.sort (by trivial)) (hBΔ.weak henv)
  let Γ := Q :: Δ
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨hΔ, _, hQ⟩
  let B := VExpr.app (.bvar 2) (.bvar 1)
  let C := C₀.liftN 2
  have hF : env.HasType univs Γ (.bvar 2) FT := .bvar (.succ (.succ .zero))
  have hzT : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  have hB : env.HasType univs Γ B (.sort (.succ .zero)) := .app hF hzT
  have W : Ctx.LiftN 2 0 Γ₀ Γ := .zero [Q, S]
  have hC : env.HasType univs Γ C (.sort (.succ .zero)) := HC₀.hasType.2.weakN henv W
  have EC : proofErase Γ C = .app (.bvar 2) (.const info.ctorName []) := by
    rw [proofErase_liftN hΓ₀ hΓ W HC₀.hasType.2, EC₀]
    rfl
  have EF : proofErase Γ (.bvar 2) = .bvar 2 := if_neg (not_isProof_function_to_sort hΓ hF)
  have EZ : proofErase Γ (.bvar 1) = .bvar 1 :=
    if_neg (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hzT)
  have EB : proofErase Γ B = .app (.bvar 2) (.bvar 1) := by
    rw [show proofErase Γ B = .app _ _ from if_neg (not_isProof_of_sort hΓ hB), EF, EZ]
  have ES : proofErase Γ S = .const family [] :=
    if_neg (not_isProof_of_sort hΓ (hS.weak0 henv.ordered))
  have RZ := proofErase_scoped_lookup_recovery (Step := ErasedUnitEtaExpansionStage D 0)
    hΓ (show Lookup Γ 1 S from .succ .zero)
    (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hzT) .refl
  rw [ES] at RZ
  have RZ' := (unit_eta_native_join hi hix hz (ps := []) hp.symm RZ RZ).1
  rw [EZ] at RZ'
  have RBC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ B) (proofErase Γ C) := by
    rw [EB, EC, ← EF]
    exact .app .refl (RZ'.mono (fun H => ⟨1, erased_unit_into_static_structure_eta_stage 1 H⟩))
  obtain ⟨C', HBC', EC'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hB rfl rfl RBC
  obtain ⟨_, HC⟩ := (proofErase_reflect hΓ HBC'.hasType.2 hC EC').2
    (not_isProof_of_sort hΓ HBC'.hasType.2)
  have HBC := HBC'.transU_l henv hΓ (HC.defeq hΓ)
  have hf : env.HasType univs Γ (.bvar 0) (.forallE (.sort (.succ .zero)) B.lift) := .bvar .zero
  have hA : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have hΓA : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have HP := IsDefEq.forallEDF hA (HBC.weakN henv Ctx.LiftN.one)
  have RPi : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE (.sort (.succ .zero)) B.lift))
      (proofErase Γ (.forallE (.sort (.succ .zero)) C.lift)) := by
    rw [show proofErase Γ (.forallE (.sort (.succ .zero)) B.lift) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ HP.hasType.1),
      show proofErase Γ (.forallE (.sort (.succ .zero)) C.lift) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ HP.hasType.2),
      proofErase_liftN hΓ hΓA Ctx.LiftN.one hB,
      proofErase_liftN hΓ hΓA Ctx.LiftN.one hC]
    exact .forallE .refl (static_structure_compute_under_domain heq hs (DomainSort.of_typed hΓ hA) RBC)
  have hx : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have happ : env.HasType univs Γ (.app (.bvar 0) (.sort .zero)) B := by
    simpa only [VExpr.inst_lift] using HasType.app hf hx
  have hn := not_proof_at_positive_type hΓ hB happ
  have RNf := proofErase_scoped_lookup_recovery (Step := ErasedStaticStructureEtaExpansionStage D 0)
    hΓ (show Lookup Γ 0 (.forallE (.sort (.succ .zero)) B.lift) from .zero)
    (not_isProof_fn hΓ hf hx hn) .refl
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.app (.bvar 0) (.sort .zero))) (proofErase Γ B) := by
    rw [show proofErase Γ (.forallE (.sort (.succ .zero)) B.lift) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ HP.hasType.1)] at RNf
    have EI := proofErase_instN hΓA hx Ctx.InstN.zero (hB.weakN henv Ctx.LiftN.one)
    simp only [VExpr.inst_lift] at EI
    rw [show proofErase Γ (.app (.bvar 0) (.sort .zero)) = .app _ _ from if_neg hn, EI]
    exact .app RNf
  refine ⟨Γ, B, C, hΓ, hB, hC, hf, HP.defeq hf, RPi, ?_, RBC, ?_⟩
  · simpa only [VExpr.inst_lift] using RN
  · intro Step hstep R
    rw [proofErase_liftN hΓ₀ hΓ W HC₀.hasType.2, EB] at R
    exact no_inserted_argument hstep hΓ₀ hΓ W HC₀.hasType.2 (j := 1) (by decide) (by decide) R

end Lean4Lean.VEnv.Strengthening
