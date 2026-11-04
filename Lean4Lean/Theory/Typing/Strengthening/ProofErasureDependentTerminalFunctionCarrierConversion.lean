import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalDomainContext

/-! # Dependent function-carrier conversion at terminal-valued domains

The induction consumes the entire finite carrier guard. It does not assume
that a body certificate can be extracted from every common comparison.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private core_forall_parts
  from Lean4Lean.Theory.Typing.Strengthening.AnchoredFamilyRecovery
open private forget_scope
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreOracleReduction
open private erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private domain_sort_raw
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
variable [Params]

private theorem convert_raw
    (hs : D.Sound env univs)
    (H : ComputedJointCheck (ErasedJointStage D 0) Δ kind sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : TerminalDomain Γ A)
    (hf : env.HasType univs Γ f (.forallE A C))
    (hg : env.HasType univs Γ g (.forallE A C))
    (EΓ : proofEraseCtx Γ = Δ) (Ef : proofErase Γ f = sa) (Eg : proofErase Γ g = sb)
    (Ek : kind = .carrier (.forallE (proofErase Γ A) (proofErase (A :: Γ) C))) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) Δ
      (.forallE (proofErase Γ B) (proofErase (A :: Γ) C)) sa sb := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedJointStage D 0) := ErasedScopedPrimitiveCertificateDescent.descent (erased_joint_zero_certificate_descent hs)
  induction H generalizing Γ A B C u f g with
  | carrierChecked H => exact .carrierChecked H
  | carrierSymm H ih => exact .carrierSymm (ih hΓ HAB HA hg hf EΓ Eg Ef Ek)
  | carrierCompute R H ih =>
    have E := JointCheckKind.carrier.inj Ek
    rw [E] at R
    obtain ⟨Ar, Br, Er, _RA, RB⟩ := core_forall_parts (forget_scope R)
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    have EPi : proofErase Γ (.forallE A C) =
        .forallE (proofErase Γ A) (proofErase (A :: Γ) C) :=
      if_neg (not_isProof_of_sort hΓ hPi)
    obtain ⟨T', HET, ET⟩ := proofErase_scoped_compute_realize hstep hΓ hPi EΓ EPi R
    obtain ⟨A', C', rfl, _, EA, EC⟩ := erase_forallE_inv (ET.trans Er)
    obtain ⟨⟨_, HEA⟩, _⟩ := HET.toU.forallE_inv henv hΓ
    have HEA := HEA.toU.of_l henv hΓ HAB.hasType.1
    have HA' : TerminalDomain Γ A' := HA.convert hΓ HEA
    have HC := ih hΓ (HEA.symm.trans HAB) HA' (HET.defeq hf) (HET.defeq hg)
      EΓ Ef Eg (by rw [EA, EC]; exact congrArg JointCheckKind.carrier Er)
    have RC : ScopedCompute (ErasedJointStage D 0) (proofErase Γ B :: proofEraseCtx Γ)
        (proofErase (A :: Γ) C) Br := RB.scoped (fun H => .base H)
    rw [EΓ] at RC
    apply ComputedJointCheck.carrierCompute (ScopedCompute.forallE .refl RC)
    simpa only [EC] using HC
  | carrierReduce Rf Rg H ih =>
    obtain ⟨f', HF, Ef'⟩ := proofErase_scoped_compute_realize hstep hΓ hf EΓ Ef Rf
    obtain ⟨g', HG, Eg'⟩ := proofErase_scoped_compute_realize hstep hΓ hg EΓ Eg Rg
    exact .carrierReduce Rf Rg (ih hΓ HAB HA HF.hasType.2 HG.hasType.2 EΓ Ef' Eg' Ek)
  | carrierFunction SD H ih =>
    obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj (JointCheckKind.carrier.inj Ek)
    have hA := domain_sort_raw SD hΓ HAB.hasType.1 EΓ rfl
    have HAB' := HAB.toU.of_l henv hΓ hA
    by_cases hp : IsProof Γ f
    · have hp' := isProof_of_common_type hΓ hf hg hp
      have Efg := Ef.symm.trans ((proofErase_eq_proof.2 hp).trans
        ((proofErase_eq_proof.2 hp').symm.trans Eg))
      exact Efg ▸ .carrierChecked (.leaf .refl)
    have hng : ¬ IsProof Γ g := fun hp' => hp (isProof_of_common_type hΓ hg hf hp')
    have hfa : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) C := by
      simpa only [lift, VExpr.liftN, inst_liftN_bvar, VExpr.inst] using HasType.app (hf.weak henv) (.bvar .zero)
    have hga : env.HasType univs (A :: Γ) (.app g.lift (.bvar 0)) C := by
      simpa only [lift, VExpr.liftN, inst_liftN_bvar, VExpr.inst] using HasType.app (hg.weak henv) (.bvar .zero)
    have Efa := proofErase_eta_body hΓ hA hf hp
    have Ega := proofErase_eta_body hΓ hA hg hng
    rw [Ef] at Efa
    rw [Eg] at Ega
    have HB := proofErase_computed_joint_zero_carrier_terminal_context hs hΓ HAB' HA hfa hga
      (by simpa only [proofEraseCtx, EΓ, Efa, Ega] using H)
    apply ComputedJointCheck.carrierFunction
      (by simpa only [EΓ] using DomainSort.of_typed hΓ HAB'.hasType.2)
    simpa only [proofEraseCtx, EΓ, Efa, Ega] using HB
  | carrierSubsingleton HS =>
    have E := JointCheckKind.carrier.inj Ek
    cases HS with
    | unit =>
      have HE := congrArg ProofShape.constHead E
      simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HE
      cases HE
    | forallE HS =>
      obtain ⟨_, rfl⟩ := ProofShape.forallE.inj E
      exact .carrierSubsingleton (.forallE HS)
  | carrierIntro | carrierNested =>
    have HE := congrArg ProofShape.constHead (JointCheckKind.carrier.inj Ek)
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HE
    cases HE
  | leaf | app | appCarrier | appComputed | proj | lam | forallE | lamSorted |
      forallSorted | lamCommon | etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases Ek

/-- Every finite dependent function-carrier guard transfers along actual
equality of its terminal-valued source domain. Carrier computation retains its
entire codomain path and replays it under the converted binder. No annotation
shape restriction, native recovery, or separately supplied body certificate
is required. -/
theorem proofErase_computed_joint_dependent_terminal_function_carrier_convert
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : TerminalDomain Γ A)
    (hf : env.HasType univs Γ f (.forallE A C))
    (hg : env.HasType univs Γ g (.forallE A C))
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) C)) (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ B) (proofErase (A :: Γ) C)) (proofErase Γ f) (proofErase Γ g) :=
  convert_raw hs H hΓ HAB HA hf hg rfl rfl rfl rfl

end Lean4Lean.VEnv.Strengthening
