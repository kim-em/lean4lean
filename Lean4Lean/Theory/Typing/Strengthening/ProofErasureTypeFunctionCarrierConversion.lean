import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalDomainContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedCarrierTypeChecking

/-! # Reading arbitrary typed carriers at dependent type-family targets

The source carrier need not display a Pi or retain the target codomain syntax.
At each exposed function guard, the eta-body guard transfers through the equal
terminal input binder and recursively reads at the target codomain. The final
universe case converts the guard to ordinary comparison using actual typing.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private domain_sort_raw from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
variable [Params]

/-- Finite dependent function targets ending in a universe. Each input has a
terminal generic value, enabling full recursive context conversion. -/
inductive TerminalTypeFamily : List VExpr → VExpr → Prop where
  | sort : TerminalTypeFamily Γ (.sort u)
  | function : TerminalDomain Γ A → TerminalTypeFamily (A :: Γ) B →
      TerminalTypeFamily Γ (.forallE A B)

/-- The target grammar survives arbitrary actual typed substitution, including
its dependent input certificates under every binder. -/
theorem TerminalTypeFamily.subst (H : TerminalTypeFamily Γ T)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hT : env.HasType univs Γ T (.sort u)) : TerminalTypeFamily Γ₀ (T.subst σ) := by
  induction H generalizing Γ₀ σ u with
  | sort => exact .sort
  | function HA HB ih =>
    obtain ⟨⟨_, hA⟩, _, hB⟩ := hT.forallE_inv henv
    exact .function (HA.subst hΓ₀ W hA)
      (ih ⟨hΓ₀, _, hA.subst henv.orderedStrong W hΓ₀⟩ (W.lift henv.ordered hA) hB)

/-- A helper interface for converting the binder of a function carrier guard.
Concrete terminal and shared-test domains discharge this interface; it is not
assumed as a new strengthening principle. -/
def ComputedCarrierBinderTransport (D : PureObservation.Definitions)
    (Γ : List VExpr) (T : VExpr) : Prop :=
  ∀ {A u f g C}, OnCtx Γ (env.IsType univs) →
    env.IsDefEq univs Γ A T (.sort u) →
    env.HasType univs (A :: Γ) f C → env.HasType univs (A :: Γ) g C →
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) C) (proofErase (A :: Γ) f) (proofErase (A :: Γ) g) →
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (T :: Γ))
      (proofErase (A :: Γ) C) (proofErase (A :: Γ) f) (proofErase (A :: Γ) g)

private theorem function_body_readout
    (transport : ComputedCarrierBinderTransport D Γ T)
    (readout : ∀ {f g A}, OnCtx (T :: Γ) (env.IsType univs) →
      env.HasType univs (T :: Γ) f A → env.HasType univs (T :: Γ) g A →
      env.IsDefEqU univs (T :: Γ) A K →
      ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (T :: Γ))
        (proofErase (T :: Γ) A) (proofErase (T :: Γ) f) (proofErase (T :: Γ) g) →
      ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (T :: Γ))
        (proofErase (T :: Γ) K) (proofErase (T :: Γ) f) (proofErase (T :: Γ) g))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A C))
    (hg : env.HasType univs Γ g (.forallE A C))
    (HE : env.IsDefEqU univs Γ (.forallE A C) (.forallE T K))
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) C)
      (.app ((proofErase Γ f).liftN 1) (etaArgument u))
      (.app ((proofErase Γ g).liftN 1) (etaArgument u))) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.forallE T K)) (proofErase Γ f) (proofErase Γ g) := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, HA⟩, ⟨_, HC⟩⟩ := HE.forallE_inv henv hΓ
  have HA := HA.toU.of_l henv hΓ hA
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have W : IsDefEqCtx env univs [] (A :: Γ) (T :: Γ) := .succ (.refl hΓ) HA
  have hΓT := (W.symm henv.ordered).isType
  have hTarget := (HE.of_l henv hΓ hPi).hasType.2
  by_cases hp : IsProof Γ f
  · have hq := isProof_of_common_type hΓ hf hg hp
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hq]
    exact .carrierChecked (.leaf .refl)
  have hq : ¬ IsProof Γ g := fun hq => hp (isProof_of_common_type hΓ hg hf hq)
  have hfa : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) C := by
    simpa only [lift, VExpr.liftN, inst_liftN_bvar, VExpr.inst] using HasType.app (hf.weak henv) (.bvar .zero)
  have hga : env.HasType univs (A :: Γ) (.app g.lift (.bvar 0)) C := by
    simpa only [lift, VExpr.liftN, inst_liftN_bvar, VExpr.inst] using HasType.app (hg.weak henv) (.bvar .zero)
  have Ef := proofErase_eta_body hΓ hA hf hp
  have Eg := proofErase_eta_body hΓ hA hg hq
  have HB := transport hΓ HA hfa hga (by simpa only [Ef, Eg] using H)
  have HC' := HC.defeqDFC henv W
  have HB' := readout hΓT (hfa.defeqDFC henv W) (hga.defeqDFC henv W) HC'.toU
    (by simpa only [← proofErase_defeqCtx hΓA W HC.hasType.1,
      ← proofErase_defeqCtx hΓA W hfa, ← proofErase_defeqCtx hΓA W hga] using HB)
  rw [← proofErase_defeqCtx hΓA W hfa, ← proofErase_defeqCtx hΓA W hga, Ef, Eg] at HB'
  rw [show proofErase Γ (.forallE T K) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hTarget)]
  exact .carrierFunction (DomainSort.of_typed hΓ HA.hasType.2) HB'

private theorem convert_raw
    (hs : D.Sound env univs) (transport : ComputedCarrierBinderTransport D Γ T)
    (readout : ∀ {f g A}, OnCtx (T :: Γ) (env.IsType univs) →
      env.HasType univs (T :: Γ) f A → env.HasType univs (T :: Γ) g A →
      env.IsDefEqU univs (T :: Γ) A K →
      ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (T :: Γ))
        (proofErase (T :: Γ) A) (proofErase (T :: Γ) f) (proofErase (T :: Γ) g) →
      ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (T :: Γ))
        (proofErase (T :: Γ) K) (proofErase (T :: Γ) f) (proofErase (T :: Γ) g))
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : ComputedJointCheck (ErasedJointStage D 0) Δ kind sa sb)
    (hf : env.HasType univs Γ f A) (hg : env.HasType univs Γ g A)
    (HE : env.IsDefEqU univs Γ A (.forallE T K))
    (EΓ : proofEraseCtx Γ = Δ)
    (E : JointCheckKind.carrier (proofErase Γ A) = kind)
    (Ef : proofErase Γ f = sa) (Eg : proofErase Γ g = sb) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) Δ
      (proofErase Γ (.forallE T K)) sa sb := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedJointStage D 0) := ErasedScopedPrimitiveCertificateDescent.descent (erased_joint_zero_certificate_descent hs)
  induction H generalizing A f g with
  | carrierChecked H => exact .carrierChecked H
  | carrierSymm H ih => exact .carrierSymm (ih hg hf HE EΓ E Eg Ef)
  | carrierReduce Rf Rg H ih =>
    obtain ⟨f', HF, Ef'⟩ := proofErase_scoped_compute_realize hstep hΓ hf EΓ Ef Rf
    obtain ⟨g', HG, Eg'⟩ := proofErase_scoped_compute_realize hstep hΓ hg EΓ Eg Rg
    exact .carrierReduce Rf Rg (ih HF.hasType.2 HG.hasType.2 HE EΓ E Ef' Eg')
  | carrierCompute R H ih =>
    obtain ⟨_, hA⟩ := hf.isType henv hΓ
    obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ
      (JointCheckKind.carrier.inj E) R
    exact ih (HA.defeq hf) (HA.defeq hg) (HA.symm.toU.trans henv hΓ HE) EΓ
      (congrArg JointCheckKind.carrier EA) Ef Eg
  | carrierFunction SD H =>
    obtain ⟨B, C, rfl, _, EB, EC⟩ := erase_forallE_inv (JointCheckKind.carrier.inj E)
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    obtain ⟨⟨_, hB⟩, _, _⟩ := hPi.forallE_inv henv
    have hB := domain_sort_raw SD hΓ hB EΓ EB
    have HG := function_body_readout transport readout hΓ hB hf hg HE
      (by simpa only [proofEraseCtx, EΓ, EB, EC, Ef, Eg] using H)
    simpa only [EΓ, Ef, Eg] using HG
  | carrierSubsingleton HS =>
    cases HS with
    | unit hi hz hf' hp =>
      obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv (JointCheckKind.carrier.inj E)
      obtain ⟨_, hA⟩ := hf.isType henv hΓ
      exact (henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
        (HE.symm.typeChain henv hΓ (HE.of_l henv hΓ hA).hasType.2)).elim
    | forallE HS =>
      obtain ⟨B, C, rfl, _, EB, EC⟩ := erase_forallE_inv (JointCheckKind.carrier.inj E)
      obtain ⟨_, hPi⟩ := hf.isType henv hΓ
      obtain ⟨⟨_, hB⟩, _, _⟩ := hPi.forallE_inv henv
      have HG := function_body_readout transport readout hΓ hB hf hg HE
        (.carrierSubsingleton (EC.symm ▸ HS))
      simpa only [EΓ, Ef, Eg] using HG
  | carrierIntro hi hz hp hadm HF | carrierNested hi hz hp hadm HT' HF =>
    obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv (JointCheckKind.carrier.inj E)
    obtain ⟨_, hA⟩ := hf.isType henv hΓ
    exact (henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
      (HE.symm.typeChain henv hΓ (HE.of_l henv hΓ hA).hasType.2)).elim
  | leaf | app | appCarrier | appComputed | proj | lam | forallE | lamSorted |
      forallSorted | lamCommon | etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases E

/-- Every typed computed carrier guard transfers to an equal finite dependent
family ending in a universe. The target grammar, rather than the guard's size,
controls recursive codomain conversion. Arbitrary source carrier computations
and endpoint reductions are consumed without a new transport assumption. -/
theorem TerminalTypeFamily.carrier_convert (HT : TerminalTypeFamily Γ T)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f A) (hg : env.HasType univs Γ g A)
    (HE : env.IsDefEqU univs Γ A T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ T) (proofErase Γ f) (proofErase Γ g) := by
  induction HT generalizing f g A with
  | sort =>
    obtain ⟨_, hA⟩ := hf.isType henv hΓ
    have HE := HE.of_l henv hΓ hA
    have hstep : ErasedScopedPrimitiveDescent (ErasedJointStage D 0) :=
      ErasedScopedPrimitiveCertificateDescent.descent (erased_joint_zero_certificate_descent hs)
    exact .carrierChecked (proofErase_computed_carrier_types_checked hstep hΓ
      (HE.defeq hf) (HE.defeq hg) (.inl hf) H)
  | function HA HC ih =>
    exact convert_raw hs
      (fun hΓ HAB hf hg H => proofErase_computed_joint_zero_carrier_terminal_context
        hs hΓ HAB (HA.convert hΓ HAB.symm) hf hg H)
      (fun hΓ hf hg HE H => ih hΓ hf hg HE H)
      hΓ H hf hg HE rfl rfl rfl rfl

/-- Every finite computed guard at an arbitrary actual source carrier transfers
to an equal type-valued function type whose input domain is terminal. Neither
a displayed source Pi, a fixed source codomain, nor native recovery is assumed.
This consumes the whole source guard, including carrier and endpoint reductions. -/
theorem proofErase_computed_joint_type_function_carrier_convert
    (hs : D.Sound env univs) (HT : TerminalDomain Γ T)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f A) (hg : env.HasType univs Γ g A)
    (HE : env.IsDefEqU univs Γ A (.forallE T (.sort v)))
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.forallE T (.sort v))) (proofErase Γ f) (proofErase Γ g) :=
  (TerminalTypeFamily.function HT .sort).carrier_convert hs hΓ hf hg HE H

end Lean4Lean.VEnv.Strengthening
