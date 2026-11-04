import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaNativeInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJoinedNativeBoundary

/-! # Native eta expansion repairs the neutral eta-assigned input

The former assigned-type obstruction is repaired at stage one. The new exact
image then instantiates dependent computation and the full aligned checker.
The earlier beta/universe join obstruction remains a valid limitation of that
smaller relation, not of the new eta-expanded system.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
namespace EtaRecoveryJoinBoundary
open private functionType familyType context native assigned nativeRaw assignedRaw
  context_wf source_typed native_typed types_equal erasures function_type function_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private raw_no_join context_pure
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJoinedNativeBoundary
variable [Params]

/-- The original eta-converted variable recovers its exact assigned type at
eta-expanded stage one, in every well-formed base context. -/
theorem native_eta_expansion_recovery (hΓ : OnCtx Γ (env.IsType univs)) :
    ScopedTypeRecovery (ErasedEtaExpansionStage D 1) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (.bvar 0)) (proofErase (context Γ) assigned) := by
  have hC := context_wf hΓ
  have hn := not_proof_at_positive_type hC native_typed source_typed
  have Ee : proofErase (context Γ) (.bvar 0) = .bvar 0 := if_neg hn
  obtain ⟨EN, EA⟩ := erasures hΓ
  have EO : contextOracle (proofEraseCtx (context Γ)) 0 = nativeRaw := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hC (Lookup.zero (ty := VExpr.app (.bvar 0) (.bvar 1)))]
    exact EN
  have ES : proofErase (context Γ) (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hC (HasType.sort (by trivial)))
  have hCP : OnCtx (.sort .zero :: context Γ) (env.IsType univs) := ⟨hC, _, HasType.sort (by trivial)⟩
  have EF : proofErase (context Γ) functionType = .forallE (.sort .zero) (.sort .zero) := by
    rw [show proofErase (context Γ) functionType = .forallE _ _ from
      if_neg (not_isProof_of_sort hC function_type), ES]
    exact congrArg (ProofShape.forallE (.sort .zero))
      (if_neg (not_isProof_of_sort hCP (HasType.sort (by trivial))))
  have RO : contextOracle (proofEraseCtx (context Γ)) 2 = .forallE (.sort .zero) (.sort .zero) := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hC
      (show Lookup (context Γ) 2 functionType from .succ (.succ .zero)), EF]
  have RF : ScopedTypeRecovery (ErasedEtaExpansionStage D 0) (proofEraseCtx (context Γ))
      (.bvar 2) (.forallE (.sort .zero) (.sort .zero)) := RO ▸ ScopedTypeRecovery.bvar
  have SD : DomainSort (proofEraseCtx (context Γ)) (.sort .zero) (.succ .zero) := by
    rw [← ES]
    exact .of_typed hC (HasType.sort (by trivial))
  have Earg : etaArgument (.succ .zero) = .bvar 0 := by
    unfold etaArgument
    split
    · rename_i H
      have := VLevel.equiv_def.1 H []
      simp [VLevel.eval] at this
    · rfl
  have RE : ErasedEtaExpansionStage D 1 (proofEraseCtx (context Γ)) (.bvar 2)
      (.lam (.sort .zero) (.app (.bvar 3) (.bvar 0))) := by
    apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
    simpa only [Earg, ProofShape.liftN, liftVar, Nat.reduceLT, ↓reduceIte, Nat.reduceAdd] using
      NativeEtaExpansion.intro RF SD
  rw [Ee, EA]
  apply ScopedTypeRecovery.convert (T := nativeRaw)
  · rw [← EO]; exact .bvar
  · exact .app .refl (.base RE)

/-- A strict repair in the same actual context: the old controlled-beta union
has no recovered output beta/universe-joined to the assigned type, while one
native eta layer recovers that assigned type exactly. -/
theorem native_eta_expansion_strict_repair (hΓ : OnCtx Γ (env.IsType univs))
    (HΓ : PureContext (proofEraseCtx Γ)) :
    (∀ T, ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (.bvar 0)) T → ¬ BetaLevelJoin T (proofErase (context Γ) assigned)) ∧
    ScopedTypeRecovery (ErasedEtaExpansionStage D 1) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (.bvar 0)) (proofErase (context Γ) assigned) := by
  refine ⟨?_, native_eta_expansion_recovery hΓ⟩
  intro T R HJ
  have hC := context_wf hΓ
  have hn := not_proof_at_positive_type hC native_typed source_typed
  obtain ⟨EN, EA⟩ := erasures hΓ
  have EO : contextOracle (proofEraseCtx (context Γ)) 0 = nativeRaw := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hC (Lookup.zero (ty := VExpr.app (.bvar 0) (.bvar 1)))]
    exact EN
  rw [show proofErase (context Γ) (.bvar 0) = .bvar 0 from if_neg hn] at R
  have RC := R.bvar_compute
  rw [EO] at RC
  have HN := erased_expansion_union_pure_join RC (context_pure HΓ) (by trivial)
  exact raw_no_join (HN.trans (by simpa only [EA] using HJ))

/-- The repaired exact image instantiates arbitrary full aligned dependent
comparisons. Its single eta guard contributes one to the target stage bound. -/
theorem native_eta_expansion_aligned_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs (assigned :: context Γ) a T)
    (hb : env.HasType univs (assigned :: context Γ) b T)
    (H : CarrierAlignedCompare (ErasedEtaExpansionStage D n) (proofEraseCtx (assigned :: context Γ)) mode
      (proofErase (assigned :: context Γ) a) (proofErase (assigned :: context Γ) b)) :
    CarrierAlignedCompare (ErasedEtaExpansionStage D (n + 1)) (proofEraseCtx (context Γ)) mode
      (proofErase (context Γ) (a.inst (.bvar 0))) (proofErase (context Γ) (b.inst (.bvar 0))) :=
  EtaNativeSubstitution.aligned_inst heq hs (context_wf hΓ) types_equal.hasType.1
    (types_equal.symm.defeq source_typed) (native_eta_expansion_recovery hΓ) ha hb H

/-- Dependent computations also instantiate through the repaired eta image. -/
theorem native_eta_expansion_compute_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs (assigned :: context Γ) e T)
    (R : ScopedCompute (ErasedEtaExpansionStage D n) (proofEraseCtx (assigned :: context Γ))
      (proofErase (assigned :: context Γ) e) out) :
    ScopedCompute (ErasedEtaExpansionStage D (n + 1)) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (e.inst (.bvar 0))) (out.inst (.bvar 0)) := by
  have hn := not_proof_at_positive_type (context_wf hΓ) native_typed source_typed
  simpa only [show proofErase (context Γ) (.bvar 0) = .bvar 0 from if_neg hn] using
    EtaNativeSubstitution.compute_inst heq hs (context_wf hΓ)
      (types_equal.symm.defeq source_typed) (native_eta_expansion_recovery hΓ) ht R

end EtaRecoveryJoinBoundary
end Lean4Lean.VEnv.Strengthening
