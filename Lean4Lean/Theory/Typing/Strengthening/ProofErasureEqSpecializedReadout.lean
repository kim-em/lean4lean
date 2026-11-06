import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPrefixSpecialization
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSpineCutReadout

/-! # Specialized Eq readout through a retained target completion

The carrier guard is lowered before its semantic equality is specialized.
At a full five-argument prefix, an additional ambient binder need not have
any target inhabitant: its guard can be descended in a separate first step.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A carrier guard on a specialized full Eq prefix reads the original target
equation. Both ambient descent and guard reflection precede semantic substitution;
pointwise completion equalities then recover the original endpoints and carrier. -/
theorem EqPrefixSpecialization.read_carrier_guard
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecialization Γ Δ v w v' w' [α,a,M,minor,b] [α',a',M',minor',b'])
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hf : env.HasType univs Γ (eqRecBeforeMajor v' w' α' a' M' minor' b') F)
    (HG : ComputedJointCarrierGuard Step (proofEraseCtx Γ')
      ((proofErase Γ α').liftN count offset)
      ((proofErase Γ a').liftN count offset) ((proofErase Γ b').liftN count offset)) :
    env.IsDefEq univs Δ a b α := by
  obtain ⟨σ, pending, WS, _, HA⟩ := H
  have hlength := HA.length_eq
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hlength
  have Eempty : pending = [] := by
    cases pending with
    | nil => rfl
    | cons x xs => simp only [List.length_cons] at hlength; omega
  subst pending
  simp only [List.map_cons, List.map_nil, List.append_nil] at HA
  cases HA with | cons _ HA =>
  cases HA with | cons Ha HA =>
  cases HA with | cons _ HA =>
  cases HA with | cons _ HA =>
  cases HA with | cons Hb HA =>
  cases HA
  obtain ⟨_, _, _, ha', _, _, hb'⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, hf⟩
  have HR := proofErase_computed_joint_carrier_reflect hstep.descent hΓ ha' hb'
    (proofErase_computed_joint_carrier_certificate_descend hstep hΓ hΓ' W ha' hb' HG)
  have HRΔ := HR.subst henv WS hΔ
  obtain ⟨_, _, _, ha, _, _, _⟩ := eqRecBeforeMajor_typings henv heq hΔ ⟨_, ht⟩
  exact ((Ha.trans henv hΔ HRΔ.toU).trans henv hΔ Hb.symm).of_l henv hΔ ha

/-- Component computation and extra trailing raw arguments do not hide the
specialized Eq guard. The first five original components recover its carrier
certificate before the target completion is read. The trailing arguments need
no actual representatives in the target context. -/
theorem EqPrefixSpecialization.read_computed_guard
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecialization Γ Δ v w v' w' [α,a,M,minor,b] [α',a',M',minor',b'])
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hf : env.HasType univs Γ (eqRecBeforeMajor v' w' α' a' M' minor' b') F)
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ'))
      ((([α',a',M',minor',b'].map (proofErase Γ)).map (·.liftN count offset)) ++ rest)
      (rawPre ++ pending))
    (HQ : ComputedJointPrefixPrimitive Step (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec levels) rawPre) target) :
    env.IsDefEq univs Δ a b α := by
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] at HA
  exact H.read_carrier_guard heq hstep hΓ hΓ' W hΔ ht hf (HQ.spine_component_guard HA)

/-- Read a specialized guard after opening an additional ambient binder.
The five source arguments are lifted across it, but no target argument is
required for that binder. Descend this guard first, then the original ambient
block, and only then specialize its semantic equation. This includes a fresh
proof-major binder without assuming a lower proof of the Eq proposition. -/
theorem EqPrefixSpecialization.read_computed_guard_under_binder
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecialization Γ Δ v w v' w' [α,a,M,minor,b] [α',a',M',minor',b'])
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hf : env.HasType univs Γ (eqRecBeforeMajor v' w' α' a' M' minor' b') F)
    (hA : env.HasType univs Γ' A (.sort u))
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx (A :: Γ')))
      (((([α',a',M',minor',b'].map (proofErase Γ)).map (·.liftN count offset)).map (·.liftN 1)) ++ rest)
      (rawPre ++ pending))
    (HQ : ComputedJointPrefixPrimitive Step (proofEraseCtx (A :: Γ'))
      (ProofShape.mkApps (.const ``Eq.rec levels) rawPre) target) :
    env.IsDefEq univs Δ a b α := by
  obtain ⟨_, _, hα', ha', _, _, hb'⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, hf⟩
  have hΓA : OnCtx (A :: Γ') (env.IsType univs) := ⟨hΓ', u, hA⟩
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] at HA
  have HG := HQ.spine_component_guard HA
  have HG' : ComputedJointCarrierGuard Step (proofEraseCtx (A :: Γ'))
      ((proofErase Γ' (α'.liftN count offset)).liftN 1)
      ((proofErase Γ' (a'.liftN count offset)).liftN 1)
      ((proofErase Γ' (b'.liftN count offset)).liftN 1) := by
    simpa only [proofErase_liftN hΓ hΓ' W hα', proofErase_liftN hΓ hΓ' W ha',
      proofErase_liftN hΓ hΓ' W hb'] using HG
  have HG₀ := proofErase_computed_joint_carrier_certificate_descend hstep hΓ' hΓA
    Ctx.LiftN.one (ha'.weakN henv W) (hb'.weakN henv W) HG'
  apply H.read_carrier_guard heq hstep hΓ hΓ' W hΔ ht hf
  simpa only [proofErase_liftN hΓ hΓ' W hα', proofErase_liftN hΓ hΓ' W ha',
    proofErase_liftN hΓ hΓ' W hb'] using HG₀

/-- At a full five-argument Eq prefix, read a computed guard in its fresh eta
body without extending the target specialization by a proof major. Native Pi
recovery supplies an actual domain for the raw binder, and that binder is
removed by carrier-certificate descent rather than filled by a lower proof. -/
theorem EqPrefixSpecialization.read_computed_guard_after_eta
    (heq : env.HasCanonicalEq)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecialization Γ Δ v w v' w' [α,a,M,minor,b] [α',a',M',minor',b'])
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hf : env.HasType univs Γ (eqRecBeforeMajor v' w' α' a' M' minor' b') F)
    (RN : ScopedTypeRecovery Guard (proofEraseCtx Γ')
      ((proofErase Γ (eqRecBeforeMajor v' w' α' a' M' minor' b')).liftN count offset)
      (.forallE rawA rawB))
    (SD : DomainSort (proofEraseCtx Γ') rawA u)
    (HA : List.Forall₂ (ScopedCompute Step (rawA :: proofEraseCtx Γ'))
      (((([α',a',M',minor',b'].map (proofErase Γ)).map (·.liftN count offset)).map (·.liftN 1)) ++
        [etaArgument u]) (rawPre ++ pending))
    (HQ : ComputedJointPrefixPrimitive Step (rawA :: proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec levels) rawPre) target) :
    env.IsDefEq univs Δ a b α := by
  obtain ⟨A, B, hfPi, EA, _⟩ := proofErase_scoped_recovered_pi_descend hguard hΓ hΓ' W hf RN
  obtain ⟨_, hPi⟩ := hfPi.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  have hA := (EA ▸ SD).descend hΓ hΓ' W hA
  have Ectx : proofEraseCtx (A.liftN count offset :: Γ') = rawA :: proofEraseCtx Γ' := by
    rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA, EA]
  exact H.read_computed_guard_under_binder heq hstep hΓ hΓ' W hΔ ht hf (hA.weakN henv W)
    (by simpa only [Ectx] using HA) (by simpa only [Ectx] using HQ)

end Lean4Lean.VEnv.Strengthening
