import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqInterleavedSupplyHistory
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSuppliedSpineReturn

/-! # Extend supplied ancestry at an actual empty-local-supply eta cut

A bare eta head has no local argument to consume. Its actual suffix therefore
retains the new lambda. The selected annotation and body paths extend the old
source history, and the actual child cut retains that extended history.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- An actual eta origin with no local arguments can only retain its lambda.
The exact annotation computation, body path, outer run and unrestricted child
minimum are preserved; the consumed alternative has an impossible argument path. -/
theorem CountedEtaFrameOrigin.empty_arguments
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : CountedEtaFrameOrigin D n Δ f A u [] endpoint ct ck cost K)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck) :
    ∃ A' body' cd cb m,
      endpoint = .lam A' body' ∧
      ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
      TypedSource (A :: Δ) (.app (f.liftN 1) (etaArgument u)) ∧
      ScopedComputeCount (PiInertStage D m) cb (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) body' ∧
      PiInertTypedContinuationRun D Ω out (A :: Δ)
        (fun body k => K (.lam A' body) k) body' ck ∧ cb+ck < cost ∧
      ∀ later j body k, ScopedComputeCount (PiInertStage D later) j (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) body → K (.lam A' body) k → cb+ck ≤ j+k := by
  obtain ⟨SD, H⟩ := H
  rcases H with
    ⟨A', body', args', cf, ca, cd, cb, m, _, _, EO, _, RA, RD, HT, RB, hsmall, HM⟩ |
    ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, _, _, _, RA, _⟩
  · cases RA
    simp only [ProofShape.mkApps] at EO HM
    have HK' := EO ▸ HK
    have HR := PiInertTypedContinuationRun.retained (args := [])
      (HT.pi_inert_compute heq hs RB.forget) SD RD
      (pi_inert_retained_frame_interpretation heq hs SD RD) HK'
    exact ⟨A', body', cd, cb, m, EO, RD, HT, RB, HR, hsmall, HM⟩
  · cases RA

/-- Reify an actual empty-local-supply eta step and extend the incoming
interleaved source history by its retained lambda. The chosen new image comes
from the existing pending target vector, not a new local actual argument. The
recorded body is classified into actual components or its exact nested cut,
while both alternatives retain the extended history and strict child minimum.
This does not yet close arbitrary supplied continuations or consumed nested eta. -/
theorem EqPrefixSpecializationAt.empty_supply_eta_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveCertificateDescent Guard Guard)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ (y :: rest))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (HH : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ historyTarget historyMap
      Γ Λ σ blocks Ξ χ plug chosen depth)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HT : TypedSource (proofEraseCtx Λ) source)
    (RN : ScopedTypeRecovery Guard (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)))
      (.forallE rawA rawB))
    (SD : DomainSort (proofEraseCtx Λ) rawA u)
    (RP : ScopedComputeCount (PiInertStage D n) cp (proofEraseCtx Λ) source
      (blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))))
    (HR : PiInertStage D n (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)))
      (.lam rawA (.app
        ((blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))).liftN 1)
        (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Λ)
      (.lam rawA (.app
        ((blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))).liftN 1)
        (etaArgument u))) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ) K endpoint ck)
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j
      (proofEraseCtx Λ) source tail → K tail k → cost ≤ j+k) :
    ∃ A B A' body' cd cb m,
      env.HasType univs Γ A (.sort u) ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B) ∧
      proofErase Λ (blocks.actual A) = rawA ∧
      EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original
        (pre.map VExpr.lift ++ [VExpr.bvar 0]) (σ.cons y) rest ∧
      EqSpecializationFrame (A :: Γ) (A.subst ρ :: Γ') Δ
        (σ.cons y) (σ'.cons y) ρ.lift τ.lift ∧
      EqFrameInsertionChain (A :: Γ) (A.subst ρ :: Γ') ρ.lift τ.lift
        (blocks.actual A :: Λ) (blocks.actual (A.subst ρ) :: Λ') κ.lift υ.lift blocks.underBinder ∧
      env.HasType univs (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B ∧
      ¬ IsProof (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) ∧
      EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ historyTarget historyMap
        (A :: Γ) (blocks.actual A :: Λ) (σ.cons y) blocks.underBinder
        (A'.subst χ :: Ξ) χ.lift (fun e => plug (.lam A' e)) (chosen+1) (depth+1) ∧
      endpoint = .lam A' body' ∧
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ)
        (blocks.erased (proofErase Γ A)) A' ∧
      TypedSource (proofEraseCtx (blocks.actual A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased)) ∧
      ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (blocks.actual A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased)) body' ∧
      PiInertTypedContinuationRun D Ω out (proofEraseCtx (blocks.actual A :: Λ))
        (fun body k => K (.lam A' body) k) body' ck ∧ cb+ck < cost ∧
      (∀ later j body k, ScopedComputeCount (PiInertStage D later) j
        (proofEraseCtx (blocks.actual A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased)) body →
        K (.lam A' body) k → cb+ck ≤ j+k) ∧
      EqChainContinuationMinimum D Δ v w original Ω out (cb+ck) ∧
      ((∃ v'' w'' pre',
        body' = ProofShape.mkApps (.const ``Eq.rec [v'',w''])
          ((pre'.map (proofErase (A :: Γ))).map blocks.underBinder.erased) ∧
        EqPrefixSpecializationAt (A :: Γ) Δ v w v'' w'' original pre' (σ.cons y) rest ∧
        env.IsDefEq univs (A :: Γ)
          (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0]))
          (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') B ∧
        List.Forall₂ (· ≈ ·) [v',w'] [v'',w''] ∧
        List.Forall₂ (ScopedCompute (PiInertStage D m) (proofEraseCtx (blocks.actual A :: Λ)))
          (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased)
          ((pre'.map (proofErase (A :: Γ))).map blocks.underBinder.erased)) ∨
      ChosenEqChainSpineCut D (A :: Γ) Δ (blocks.actual A :: Λ) blocks.underBinder v w original
        (σ.cons y) rest m
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased)) body' cb) := by
  obtain ⟨A, B, hA, hfPi, Ectx, HP, WF, JF, hb, hnb, EB⟩ :=
    H.eta_insertion_chain hguard hΔ W J ht hf hn RN SD
  have EA : proofErase Λ (blocks.actual A) = rawA := (List.cons.inj Ectx).1
  have HO := pi_inert_eta_frame_origin heq hs hguard.descent
    (args := []) (by simpa only [ProofShape.mkApps] using HT.pi_inert_compute heq hs RP.forget)
    RN SD (by simpa only [ProofShape.mkApps] using RP) HR
    (by simpa only [ProofShape.mkApps] using RT) HK.holds hcost HM
  obtain ⟨A', body', cd, cb, m, EO, RD, HTb, RB, HRb, hsmall, HMbody⟩ := HO.empty_arguments heq hs HK
  have hy : env.HasType univs Δ y (A.subst σ) := by
    cases HP.1 with | cons _ _ hy => exact hy.hasType.1
  have RD : ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ A)) A' := by
    simpa only [← EA, J.erase_actual W hA] using RD
  have HHnew := EqInterleavedSupplyHistory.retained (args := []) HH hA hy RD
  have EB : ProofShape.mkApps (.const ``Eq.rec [v',w'])
      (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased) =
      .app ((blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))).liftN 1)
        (etaArgument u) := by
    simpa only [proofErase_const_spine HP.1.wf hb hnb, EqInsertionPath.erased_const_spine] using EB
  rw [← Ectx] at HTb RB HRb HMbody
  rw [← EB] at HTb RB HMbody
  have HMchain : EqChainContinuationMinimum D Δ v w original Ω out (cb+ck) := by
    refine ⟨_, _, _, _, _, _, _, _, _, _, blocks.underBinder, v', w',
      pre.map VExpr.lift ++ [VExpr.bvar 0], rest, [], B, HP, WF, JF, hb, hnb, .inl rfl, ?_⟩
    simpa only [List.append_nil] using
      (show PiInertTypedContinuationMinimum D Ω out (proofEraseCtx (blocks.actual A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased))
        (cb+ck) from ⟨_, m, cb, ck, body', HTb, RB, HRb, rfl, HMbody⟩)
  refine ⟨A, B, A', body', cd, cb, m, hA, hfPi, EA, HP, WF, JF, hb, hnb,
    HHnew, EO, RD, HTb, RB, HRb, hsmall, HMbody, HMchain, ?_⟩
  rcases HP.chain_counted_spine_or_cut heq hs hΔ WF JF hb hnb (extra := []) (.inl rfl)
      (by simpa only [List.append_nil] using HTb) (by simpa only [List.append_nil] using RB) with
    ⟨v'', w'', pre', extra', EO, HP', HE, HL, HA, Hempty, _⟩ | Hcut
  · cases Hempty
    exact .inl ⟨v'', w'', pre', by simpa only [List.append_nil] using EO, HP', HE, HL,
      by simpa only [List.append_nil] using HA⟩
  · exact .inr (by simpa only [List.append_nil] using Hcut)

/-- Classify an actual non-level cut with a nonempty target pending vector
but no local actual arguments. Positive guards recover the original equation;
otherwise its selected eta suffix extends the supplied ancestry and reads the
actual child body into components or an exact nested cut. Neither eta nor a
retained-history extension is assumed as a separate premise. -/
theorem EqPrefixSpecializationAt.empty_supply_cut_eq_or_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' [α,a,M,minor,b] pre σ (y :: rest))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (HH : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ historyTarget historyMap
      Γ Λ σ blocks Ξ χ plug chosen depth)
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HT : TypedSource (proofEraseCtx Λ) source)
    (RP : ScopedComputeCount (PiInertStage D n) cp (proofEraseCtx Λ) source
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map blocks.erased)))
    (HR : PiInertStage D n (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map blocks.erased)) target)
    (HN : ¬ LevelPrimitive univs
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map blocks.erased)) target)
    (RT : ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Λ) target endpoint)
    (HK : PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ) K endpoint ck)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU))
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j
      (proofEraseCtx Λ) source tail → K tail k → cost ≤ j+k) :
    env.IsDefEq univs Δ a b α ∨ ∃ u rawA,
      target = .lam rawA (.app
        ((ProofShape.mkApps (.const ``Eq.rec [v',w'])
          ((pre.map (proofErase Γ)).map blocks.erased)).liftN 1) (etaArgument u)) ∧
    ∃ A B A' body' cd cb m,
      env.HasType univs Γ A (.sort u) ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B) ∧
      proofErase Λ (blocks.actual A) = rawA ∧
      EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' [α,a,M,minor,b]
        (pre.map VExpr.lift ++ [VExpr.bvar 0]) (σ.cons y) rest ∧
      EqSpecializationFrame (A :: Γ) (A.subst ρ :: Γ') Δ
        (σ.cons y) (σ'.cons y) ρ.lift τ.lift ∧
      EqFrameInsertionChain (A :: Γ) (A.subst ρ :: Γ') ρ.lift τ.lift
        (blocks.actual A :: Λ) (blocks.actual (A.subst ρ) :: Λ') κ.lift υ.lift blocks.underBinder ∧
      env.HasType univs (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B ∧
      ¬ IsProof (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) ∧
      EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ historyTarget historyMap
        (A :: Γ) (blocks.actual A :: Λ) (σ.cons y) blocks.underBinder
        (A'.subst χ :: Ξ) χ.lift (fun e => plug (.lam A' e)) (chosen+1) (depth+1) ∧
      endpoint = .lam A' body' ∧
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ)
        (blocks.erased (proofErase Γ A)) A' ∧
      TypedSource (proofEraseCtx (blocks.actual A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased)) ∧
      ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (blocks.actual A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased)) body' ∧
      PiInertTypedContinuationRun D Ω out (proofEraseCtx (blocks.actual A :: Λ))
        (fun body k => K (.lam A' body) k) body' ck ∧ cb+ck < cost ∧
      (∀ later j body k, ScopedComputeCount (PiInertStage D later) j
        (proofEraseCtx (blocks.actual A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased)) body →
        K (.lam A' body) k → cb+ck ≤ j+k) ∧
      EqChainContinuationMinimum D Δ v w [α,a,M,minor,b] Ω out (cb+ck) ∧
      ((∃ v'' w'' pre',
        body' = ProofShape.mkApps (.const ``Eq.rec [v'',w''])
          ((pre'.map (proofErase (A :: Γ))).map blocks.underBinder.erased) ∧
        EqPrefixSpecializationAt (A :: Γ) Δ v w v'' w'' [α,a,M,minor,b] pre' (σ.cons y) rest ∧
        env.IsDefEq univs (A :: Γ)
          (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0]))
          (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') B ∧
        List.Forall₂ (· ≈ ·) [v',w'] [v'',w''] ∧
        List.Forall₂ (ScopedCompute (PiInertStage D m) (proofEraseCtx (blocks.actual A :: Λ)))
          (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased)
          ((pre'.map (proofErase (A :: Γ))).map blocks.underBinder.erased)) ∨
      ChosenEqChainSpineCut D (A :: Γ) Δ (blocks.actual A :: Λ) blocks.underBinder v w [α,a,M,minor,b]
        (σ.cons y) rest m
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased)) body' cb) := by
  have Eraw : blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)) =
      ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map blocks.erased) := by
    rw [proofErase_const_spine H.1.wf hf hn, EqInsertionPath.erased_const_spine]
  have HP := (H.chain_prefix_completion W J hf hn).embedding
  rcases HP.hole_cut_eq_or_smaller heq hs hreg hoff hRec hΔ ht (C := .hole)
      .hole HT RP HR HN RT HK HE HO hcost HM with
    Hlower | ⟨k, rawA, rawB, u, rfl, _, RN, SD, _, _, _⟩
  · exact .inl Hlower
  · have HHnext := H.empty_supply_eta_history heq hs
      (erased_static_structure_eta_expansion_stage_certificate_descent heq hs k) hΔ W J HH ht hf hn HT
      (by simpa only [Eraw] using RN) SD (by simpa only [Eraw] using RP)
      (by simpa only [Eraw] using HR) (by simpa only [Eraw] using RT) HK hcost HM
    exact .inr ⟨u, rawA, rfl, HHnext⟩

end Lean4Lean.VEnv.Strengthening
