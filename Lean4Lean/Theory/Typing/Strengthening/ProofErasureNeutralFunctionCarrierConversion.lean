import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralImageTransport

/-! # Whole function-carrier conversion at neutral domains

The induction consumes the entire finite carrier guard. It does not assume
that a body certificate can be extracted from every common comparison.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private core_forall_parts
  from Lean4Lean.Theory.Typing.Strengthening.AnchoredFamilyRecovery
open private forget_scope
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreOracleReduction
open private domain_sort_raw
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
variable [Params]

private theorem convert_raw
    (hs : D.Sound env univs)
    (H : ComputedJointCheck (ErasedJointStage D 0) Δ kind sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : AnchoredCarrier 0 (proofErase Γ A))
    (hf : env.HasType univs Γ f (.forallE A (.sort v)))
    (hg : env.HasType univs Γ g (.forallE A (.sort v)))
    (EΓ : proofEraseCtx Γ = Δ) (Ef : proofErase Γ f = sa) (Eg : proofErase Γ g = sb)
    (Ek : kind = .carrier (.forallE (proofErase Γ A) (.sort v))) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) Δ
      (.forallE (proofErase Γ B) (.sort v)) sa sb := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedJointStage D 0) := ErasedScopedPrimitiveCertificateDescent.descent (erased_joint_zero_certificate_descent hs)
  induction H generalizing Γ A B u v f g with
  | carrierChecked H => exact .carrierChecked H
  | carrierSymm H ih => exact .carrierSymm (ih hΓ HAB HA hg hf EΓ Eg Ef Ek)
  | carrierCompute R H ih =>
    have E := JointCheckKind.carrier.inj Ek
    rw [E] at R
    obtain ⟨Ar, Br, Er, RA, RB⟩ := core_forall_parts (forget_scope R)
    have RC : ScopedCompute (ErasedJointStage D 0) [] (.sort v) Br := RB.scoped (fun H => .base H)
    have EB := RC.sort_fixed (erased_joint_stage_head 0)
    rw [EB] at Er
    have RDA : ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ A) Ar :=
      RA.scoped (fun H => .base H)
    obtain ⟨A', HEA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ HAB.hasType.1 rfl rfl RDA
    have HA' : AnchoredCarrier 0 (proofErase Γ A') := by
      rw [EA]
      exact HA.compute (erased_joint_stage_head 0) RDA
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    obtain ⟨_, _, hv⟩ := hPi.forallE_inv henv
    have HPi := IsDefEq.forallEDF HEA (HasType.sort (hv.sort_inv henv))
    exact ih hΓ (HEA.symm.trans HAB) HA' (HPi.defeq hf) (HPi.defeq hg)
      EΓ Ef Eg (by rw [EA]; exact congrArg JointCheckKind.carrier Er)
  | carrierReduce Rf Rg H ih =>
    obtain ⟨f', HF, Ef'⟩ := proofErase_scoped_compute_realize hstep hΓ hf EΓ Ef Rf
    obtain ⟨g', HG, Eg'⟩ := proofErase_scoped_compute_realize hstep hΓ hg EΓ Eg Rg
    exact .carrierReduce Rf Rg (ih hΓ HAB HA HF.hasType.2 HG.hasType.2 EΓ Ef' Eg' Ek)
  | carrierFunction SD H ih =>
    obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj (JointCheckKind.carrier.inj Ek)
    have hA := domain_sort_raw SD hΓ HAB.hasType.1 EΓ rfl
    have HAB' := HAB.toU.of_l henv hΓ hA
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
    have hfa : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) (.sort v) := by
      simpa only [lift, VExpr.liftN, inst_liftN_bvar, VExpr.inst] using HasType.app (hf.weak henv) (.bvar .zero)
    have hga : env.HasType univs (A :: Γ) (.app g.lift (.bvar 0)) (.sort v) := by
      simpa only [lift, VExpr.liftN, inst_liftN_bvar, VExpr.inst] using HasType.app (hg.weak henv) (.bvar .zero)
    have Efa := proofErase_eta_body hΓ hA hf (not_isProof_function_to_sort hΓ hf)
    have Ega := proofErase_eta_body hΓ hA hg (not_isProof_function_to_sort hΓ hg)
    rw [Ef] at Efa
    rw [Eg] at Ega
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    obtain ⟨_, _, hv⟩ := hPi.forallE_inv henv
    have EU : proofErase (A :: Γ) (.sort v) = .sort v :=
      if_neg (not_isProof_of_sort hΓA hv)
    have HB := proofErase_computed_joint_zero_carrier_neutral_context hs hΓ HAB' HA hfa hga
      (by simpa only [proofEraseCtx, EΓ, EU, Efa, Ega] using H)
    apply ComputedJointCheck.carrierFunction
      (by simpa only [EΓ] using DomainSort.of_typed hΓ HAB'.hasType.2)
    simpa only [proofEraseCtx, EΓ, EU, Efa, Ega] using HB
  | carrierSubsingleton HS =>
    have E := JointCheckKind.carrier.inj Ek
    cases HS with
    | unit =>
      have HE := congrArg ProofShape.constHead E
      simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HE
      cases HE
    | forallE HS =>
      obtain ⟨_, rfl⟩ := ProofShape.forallE.inj E
      exact (HS.not_sort rfl).elim
  | carrierIntro | carrierNested =>
    have HE := congrArg ProofShape.constHead (JointCheckKind.carrier.inj Ek)
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HE
    cases HE
  | leaf | app | appCarrier | appComputed | proj | lam | forallE | lamSorted |
      forallSorted | lamCommon | etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases Ek

/-- Every finite carrier guard at a function type into a sort transfers along
actual equality of its neutral source domain. Endpoint reductions are
realized at their original type; carrier reductions replay their actual domain conversion.
No future-body premise or recovery-completeness hypothesis is required. -/
theorem proofErase_computed_joint_neutral_function_carrier_convert
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : AnchoredCarrier 0 (proofErase Γ A))
    (hf : env.HasType univs Γ f (.forallE A (.sort v)))
    (hg : env.HasType univs Γ g (.forallE A (.sort v)))
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (.sort v)) (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ B) (.sort v)) (proofErase Γ f) (proofErase Γ g) :=
  convert_raw hs H hΓ HAB HA hf hg rfl rfl rfl rfl

end Lean4Lean.VEnv.Strengthening
