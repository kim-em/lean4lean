import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureProbeConversion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaCertifiedProbe
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFamilyCompositionBoundary

/-! # A repaired future-carrier composition with non-joining indices

Two primitive-free future links through a typed unit constructor still cannot
compose at stage zero. An explicit future certificate for the type conversion
constructs their full future composite in the union. Its proposition indices
have no union computation join, so joining those indices is not required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private functionType function_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaCertifiedProbe
open private unit_constructor_bridge
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTypedCompositionBoundary
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- Retained type-conversion evidence repairs the typed unit/probe composition
with a full future output certificate. The source links use no primitive
computation, stage zero has no composite, and the proposition indices have
no common computational output even in the full union. -/
theorem future_unit_probe_composition_nonjoining_indices
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ P Q q B m, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ P (.sort .zero) ∧ env.HasType univs Γ Q (.sort .zero) ∧
      env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q) ∧
      B = eqTypeProbe (.succ u) (.const family ls) P Q q ∧
      env.HasType univs Γ (.bvar 1) B ∧ env.HasType univs Γ m B ∧
      env.HasType univs Γ (.bvar 2) B ∧
      BetaStableCarrier (fun _ _ _ => False) (proofEraseCtx Γ) (proofErase Γ B)
        (proofErase Γ (.bvar 1)) (proofErase Γ m) ∧
      BetaStableCarrier (fun _ _ _ => False) (proofEraseCtx Γ) (proofErase Γ B)
        (proofErase Γ m) (proofErase Γ (.bvar 2)) ∧
      BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ B)
        (proofErase Γ (.bvar 1)) (proofErase Γ (.bvar 2)) ∧
      (¬ JointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ B)
        (proofErase Γ (.bvar 1)) (proofErase Γ (.bvar 2))) ∧
      ¬ ∃ shared, ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ P) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ Q) shared := by
  let S := VExpr.const family ls
  have hΓ : OnCtx [S, S] (env.IsType univs) := ⟨⟨trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩
  obtain ⟨P, Q, q, hP, hQ, hq, HF, Hno⟩ := EtaCertifiedProbe.no_join_indices heq hEq hΓ
  let Γ := functionType :: [S, S]
  have hC : OnCtx Γ (env.IsType univs) := ⟨hΓ, _, function_type⟩
  have hSC : env.HasType univs Γ S (.sort (.succ u)) := hS.weak0 henv.ordered
  have hiT : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  have hjT : env.HasType univs Γ (.bvar 2) S := .bvar (.succ (.succ .zero))
  have HPQ := proofErase_joint_carrier_reflect (erased_joint_union_descent heq hs)
    hC hP hQ (.carrierChecked HF.base)
  have HE := eqTypeProbe_defeq heq hC hSC hP hQ hq HPQ.toU
  obtain ⟨hm, Em, _⟩ := unit_constructor_bridge (Step := fun _ _ _ => False) hC hi hp hx hf hSC hiT
  refine ⟨Γ, P, Q, q, _, .const info.ctorName ls, hC, hP, hQ, hq, rfl,
    HE.symm.defeq hiT, HE.symm.defeq hm, HE.symm.defeq hjT, ?_, ?_, ?_, ?_, Hno⟩
  · rw [Em]
    exact (unit_constructor_family hi hp hx hf).joint_symm.carrier
  · rw [Em]
    exact (unit_constructor_family hi hp hx hf).carrier
  · apply eqTypeProbe_future_subsingleton_of_family heq hs hregistry hC hSC hP hQ hq HF
    rw [show proofErase Γ S = .const family ls from if_neg (not_isProof_of_sort hC hSC)]
    exact .unit hi hx hf (ps := []) hp.symm
  · rw [show proofErase Γ (.bvar 1) = .bvar 1 from
      if_neg (not_proof_at_positive_type hC hSC hiT),
      show proofErase Γ (.bvar 2) = .bvar 2 from
      if_neg (not_proof_at_positive_type hC hSC hjT)]
    exact eqTypeProbe_zero_no_distinct_guard heq hregistry hRec hC hSC hP hQ hq (by decide)

end Lean4Lean.VEnv.Strengthening
