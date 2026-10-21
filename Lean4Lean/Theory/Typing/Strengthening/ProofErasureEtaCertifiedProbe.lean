import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStableProbeTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

/-! # A certified Eq probe whose proposition indices have no computation join

The propositions Eq f f and Eq f (fun x => f x) have different normal erasures
when f is a variable. Function eta nevertheless supplies future certificates
for them, and hence certified computation of their type-valued Eq probe.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]
namespace EtaCertifiedProbe

private def functionType : VExpr := .forallE (.sort .zero) (.sort .zero)
private def functionRaw : ProofShape := .forallE (.sort .zero) (.sort .zero)
private def etaRaw : ProofShape := .lam (.sort .zero) (.app (.bvar 1) (.bvar 0))
private def level : VLevel := .imax (.succ .zero) (.succ .zero)
private def leftRaw : ProofShape := ProofShape.eqProofType level functionRaw (.bvar 0) (.bvar 0)
private def rightRaw : ProofShape := ProofShape.eqProofType level functionRaw (.bvar 0) etaRaw

private theorem function_type : env.HasType univs Γ functionType (.sort level) :=
  .forallE (.sort (by trivial)) (.sort (by trivial))

private theorem erasures (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase (functionType :: Γ) functionType = functionRaw ∧
    proofErase (functionType :: Γ) (.bvar 0) = .bvar 0 ∧
    proofErase (functionType :: Γ) (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0))) = etaRaw := by
  have hC : OnCtx (functionType :: Γ) (env.IsType univs) := ⟨hΓ, _, function_type⟩
  have hf : env.HasType univs (functionType :: Γ) (.bvar 0) functionType := .bvar .zero
  have hη := (IsDefEq.eta hf).hasType.1
  have hC' : OnCtx (.sort .zero :: functionType :: Γ) (env.IsType univs) :=
    ⟨hC, _, HasType.sort (by trivial)⟩
  have hf' : env.HasType univs (.sort .zero :: functionType :: Γ) (.bvar 1) functionType :=
    .bvar (.succ .zero)
  have hx : env.HasType univs (.sort .zero :: functionType :: Γ) (.bvar 0) (.sort .zero) := .bvar .zero
  have hbody : env.HasType univs (.sort .zero :: functionType :: Γ)
      (.app (.bvar 1) (.bvar 0)) (.sort .zero) := .app hf' hx
  refine ⟨?_, if_neg (not_isProof_function_to_sort hC hf), ?_⟩
  · rw [show proofErase (functionType :: Γ) functionType = .forallE _ _ from
      if_neg (not_isProof_of_sort hC function_type)]
    rw [show proofErase (functionType :: Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hC (HasType.sort (by trivial))),
      show proofErase (.sort .zero :: functionType :: Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hC' (HasType.sort (by trivial)))]
    rfl
  · rw [show proofErase (functionType :: Γ) (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0))) = .lam _ _ from
      if_neg (not_isProof_function_to_sort hC hη)]
    rw [show proofErase (functionType :: Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hC (HasType.sort (by trivial))),
      show proofErase (.sort .zero :: functionType :: Γ) (.app (.bvar 1) (.bvar 0)) = .app _ _ from
      if_neg (not_isProof_of_sort hC' hbody),
      show proofErase (.sort .zero :: functionType :: Γ) (.bvar 1) = .bvar 1 from
      if_neg (not_isProof_function_to_sort hC' hf'),
      show proofErase (.sort .zero :: functionType :: Γ) (.bvar 0) = .bvar 0 from
      if_neg (not_isProof_of_sort hC' hx)]
    rfl

private theorem normal_forms (heq : env.HasCanonicalEq)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs) (Δ) :
    NormalSyntax (ErasedJointUnion D Δ) leftRaw ∧
    NormalSyntax (ErasedJointUnion D Δ) rightRaw := by
  have hv (i) : NormalSyntax (ErasedJointUnion D Δ) (.bvar i) :=
    ⟨fun _ H => erased_joint_union_head H, trivial⟩
  have hs : NormalSyntax (ErasedJointUnion D Δ) (.sort .zero) :=
    ⟨fun _ H => erased_joint_union_head H, trivial⟩
  have hfun : NormalSyntax (ErasedJointUnion D Δ) functionRaw :=
    ⟨fun _ H => erased_joint_union_head H, hs, hs⟩
  have hη : NormalSyntax (ErasedJointUnion D Δ) etaRaw :=
    ⟨fun _ H => erased_joint_union_head H, hs,
      (fun _ H => erased_joint_union_head H), (fun _ _ H => nomatch H), hv 1, hv 0⟩
  have head args out : ¬ ErasedJointUnion D Δ (ProofShape.mkApps (.const ``Eq [level]) args) out :=
    fun H => erased_joint_union_no_rigid heq (heq.rigid henv) hEq H (constHead_mkApps _ _)
  constructor
  · exact NormalSyntax.mkApps (args := [functionRaw, .bvar 0, .bvar 0])
      (fun args out _ => head args out)
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> first | exact hfun | exact hv 0 | exact hη)
  · exact NormalSyntax.mkApps (args := [functionRaw, .bvar 0, etaRaw])
      (fun args out _ => head args out)
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> first | exact hfun | exact hv 0 | exact hη)

/-- Typed proposition indices with a future eta certificate and no full-union
computational join. Their exact context is exposed for carrier/conversion tests. -/
theorem no_join_indices
    {Step : List ProofShape → ProofShape → ProofShape → Prop}
    (heq : env.HasCanonicalEq)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ P Q q,
      env.HasType univs (functionType :: Γ) P (.sort .zero) ∧
      env.HasType univs (functionType :: Γ) Q (.sort .zero) ∧
      env.HasType univs (functionType :: Γ) q (eqApp (.succ .zero) (.sort .zero) P Q) ∧
      BetaStableFamily (fun Δ => JointCompare Step Δ true)
        (proofEraseCtx (functionType :: Γ)) (proofErase (functionType :: Γ) P) (proofErase (functionType :: Γ) Q) ∧
      ¬ ∃ shared,
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx (functionType :: Γ)) (proofErase (functionType :: Γ) P) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx (functionType :: Γ)) (proofErase (functionType :: Γ) Q) shared := by
  have hC : OnCtx (functionType :: Γ) (env.IsType univs) := ⟨hΓ, _, function_type⟩
  have hf : env.HasType univs (functionType :: Γ) (.bvar 0) functionType := .bvar .zero
  have HE := IsDefEq.eta hf
  have Hη := (proofErase_function_eta_family (Step := Step) hC hf).joint_symm
  have HPQ := proofErase_stable_eq_family heq (by trivial) hC function_type hf HE.hasType.1 Hη
  have hP := HasType.eqApp heq (by trivial) function_type hf hf
  have hQ := HasType.eqApp heq (by trivial) function_type hf HE.hasType.1
  have Hactual := IsDefEq.eqApp_r heq (by trivial) function_type hf HE.symm
  have hS : env.HasType univs (functionType :: Γ) (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hq := (IsDefEq.eqApp_r heq (by trivial) hS hP Hactual).defeq
    (HasType.eqReflApp heq (by trivial) hS hP)
  refine ⟨_, _, _, hP, hQ, hq, HPQ, ?_⟩
  rintro ⟨shared, RP, RQ⟩
  obtain ⟨Eα, Ef, Eη⟩ := erasures hΓ
  rw [proofErase_eqProofType heq (by trivial) hC function_type hf hf, Eα, Ef] at RP
  change proofErase (functionType :: Γ)
    (.lam (.sort .zero) (.app (VExpr.bvar 0).lift (.bvar 0))) = etaRaw at Eη
  rw [proofErase_eqProofType heq (by trivial) hC function_type hf HE.hasType.1, Eα, Ef, Eη] at RQ
  have EP := scoped_normal_fixed RP (fun Δ => (normal_forms heq hEq Δ).1)
  have EQ := scoped_normal_fixed RQ (fun Δ => (normal_forms heq hEq Δ).2)
  cases EP.symm.trans EQ

/-- A type probe computes with a certified eta-family guard even though its
well-typed proposition indices have no join in the full joint union. The
context adds only a function variable; no extra environment declaration is needed. -/
theorem no_join_probe_computes
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' P Q q, OnCtx Γ' (env.IsType univs) ∧
      env.HasType univs Γ' P (.sort .zero) ∧ env.HasType univs Γ' Q (.sort .zero) ∧
      env.HasType univs Γ' q (eqApp (.succ .zero) (.sort .zero) P Q) ∧
      BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
        (proofEraseCtx Γ') (proofErase Γ' P) (proofErase Γ' Q) ∧
      (¬ ∃ shared, ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' P) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' Q) shared) ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ')
        (proofErase Γ' (eqTypeProbe (.succ .zero) (.sort .zero) P Q q)) (proofErase Γ' (.sort .zero)) := by
  obtain ⟨P, Q, q, hP, hQ, hq, HF, Hno⟩ := no_join_indices (Step := ErasedJointUnion D) heq hEq hΓ
  have hC : OnCtx (functionType :: Γ) (env.IsType univs) := ⟨hΓ, _, function_type⟩
  have hS : env.HasType univs (functionType :: Γ) (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  exact ⟨_, P, Q, q, hC, hP, hQ, hq, HF, Hno,
    eqTypeProbe_compute_certified_of_family heq hs hregistry hC hS hP hQ hq HF⟩

end EtaCertifiedProbe
end Lean4Lean.VEnv.Strengthening
