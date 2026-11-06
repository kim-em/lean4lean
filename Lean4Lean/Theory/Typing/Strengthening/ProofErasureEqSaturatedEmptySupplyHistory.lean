import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqEmptySupplyHistory

/-! # Record actual unused ancestry at saturated empty-local-supply cuts

A saturated bare head also retains its new eta binder. That binder is unused
by the chosen lower prefix: the history records an upper insertion, and the
native eta argument becomes an untracked upper extra in the actual body.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Realize a saturated bare-head eta and record its actual retained unused
binder. The lower assignment stays fixed; every old upper extra is lifted and
the native eta argument is appended. The child body is classified from its
actual counted path, with the new history retained in both alternatives. -/
theorem EqPrefixSpecializationAt.saturated_empty_supply_eta_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveCertificateDescent Guard Guard)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ [])
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (HH : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ historyTarget historyMap
      Γ Λ σ blocks Ξ χ plug chosen depth)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HT : TypedSource (proofEraseCtx Λ) source)
    (RN : ScopedTypeRecovery Guard (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))
      (.forallE rawA rawB))
    (SD : DomainSort (proofEraseCtx Λ) rawA u)
    (RP : ScopedComputeCount (PiInertStage D n) cp (proofEraseCtx Λ) source
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)))
    (HR : PiInertStage D n (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))
      (.lam rawA (.app
        ((ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)).liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Λ)
      (.lam rawA (.app
        ((ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)).liftN 1) (etaArgument u))) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ) K endpoint ck)
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j
      (proofEraseCtx Λ) source tail → K tail k → cost ≤ j+k) :
    ∃ A A' body' cd cb m,
      env.HasType univs Λ A (.sort u) ∧ proofErase Λ A = rawA ∧
      EqFrameInsertionChain Γ Γ' ρ τ (A :: Λ) (A.subst κ :: Λ') κ.lift υ.lift (blocks ++ [(1,0)]) ∧
      EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ historyTarget historyMap
        Γ (A :: Λ) σ (blocks ++ [(1,0)]) (A'.subst χ :: Ξ) χ.lift
        (fun e => plug (.lam A' e)) chosen (depth+1) ∧
      endpoint = .lam A' body' ∧
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ) (proofErase Λ A) A' ∧
      TypedSource (proofEraseCtx (A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
            (extra.map (·.liftN 1) ++ [etaArgument u]))) ∧
      ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
            (extra.map (·.liftN 1) ++ [etaArgument u]))) body' ∧
      PiInertTypedContinuationRun D Ω out (proofEraseCtx (A :: Λ))
        (fun body k => K (.lam A' body) k) body' ck ∧ cb+ck < cost ∧
      (∀ later j body k, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx (A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
            (extra.map (·.liftN 1) ++ [etaArgument u]))) body →
        K (.lam A' body) k → cb+ck ≤ j+k) ∧
      EqChainContinuationMinimum D Δ v w original Ω out (cb+ck) ∧
      ((∃ v'' w'' pre' extra',
        body' = ProofShape.mkApps (.const ``Eq.rec [v'',w''])
          (((pre'.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++ extra') ∧
        EqPrefixSpecializationAt Γ Δ v w v'' w'' original pre' σ [] ∧
        env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
          (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F ∧
        List.Forall₂ (· ≈ ·) [v',w'] [v'',w''] ∧
        List.Forall₂ (ScopedCompute (PiInertStage D m) (proofEraseCtx (A :: Λ)))
          (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
            (extra.map (·.liftN 1) ++ [etaArgument u]))
          (((pre'.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++ extra') ∧
        List.Forall₂ (ScopedCompute (PiInertStage D m) (proofEraseCtx (A :: Λ)))
          (extra.map (·.liftN 1) ++ [etaArgument u]) extra') ∨
      ChosenEqChainSpineCut D Γ Δ (A :: Λ) (blocks ++ [(1,0)]) v w original σ [] m
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
            (extra.map (·.liftN 1) ++ [etaArgument u]))) body' cb) := by
  have HTwhole := HT.pi_inert_compute heq hs RP.forget
  obtain ⟨A, hA, EA, JF⟩ := J.open_recovered_domain hguard.descent W HTwhole RN SD
  have HO := pi_inert_eta_frame_origin heq hs hguard.descent
    (args := []) (by simpa only [ProofShape.mkApps] using HTwhole) RN SD
    (by simpa only [ProofShape.mkApps] using RP) HR
    (by simpa only [ProofShape.mkApps] using RT) HK.holds hcost HM
  obtain ⟨A', body', cd, cb, m, EO, RD, HTb, RB, HRb, hsmall, HMbody⟩ := HO.empty_arguments heq hs HK
  have Ectx : proofEraseCtx (A :: Λ) = rawA :: proofEraseCtx Λ := by
    simp only [proofEraseCtx, EA]
  have RD : ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ) (proofErase Λ A) A' := EA.symm ▸ RD
  have HHnew := EqInterleavedSupplyHistory.unused (args := []) HH hA RD
  have EB : ProofShape.mkApps (.const ``Eq.rec [v',w'])
      (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
        (extra.map (·.liftN 1) ++ [etaArgument u])) =
      .app ((ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)).liftN 1) (etaArgument u) := by
    simp only [ProofShape.liftN_mkApps, ProofShape.liftN, ProofShape.mkApps_append,
      ProofShape.mkApps, List.map_map, Function.comp_def, EqInsertionPath.erased_snoc]
  rw [← Ectx] at HTb RB HRb HMbody
  rw [← EB] at HTb RB HMbody
  have HMchain : EqChainContinuationMinimum D Δ v w original Ω out (cb+ck) :=
    ⟨Γ, Γ', A :: Λ, A.subst κ :: Λ', σ, σ', ρ, τ, κ.lift, υ.lift, blocks ++ [(1,0)],
      v', w', pre, [], extra.map (·.liftN 1) ++ [etaArgument u], F,
      H, W, JF, hf, hn, .inr rfl, _, m, cb, ck, body', HTb, RB, HRb, rfl, HMbody⟩
  refine ⟨A, A', body', cd, cb, m, hA, EA, JF, HHnew, EO, RD, HTb, RB, HRb, hsmall, HMbody, HMchain, ?_⟩
  rcases H.chain_counted_spine_or_cut heq hs hΔ W JF hf hn (.inr rfl) HTb RB with
    ⟨v'', w'', pre', extra', EO, HP, HE, HL, HA, HX, _⟩ | Hcut
  · exact .inl ⟨v'', w'', pre', extra', EO, HP, HE, HL, HA, HX⟩
  · exact .inr Hcut

/-- Classify an actual saturated non-level cut at the whole reached spine,
so there is no local suffix outside the cut. Its native eta alternative derives
the unused-history extension and keeps every upper extra in the actual child
readout. Positive guards instead recover the original target equation. -/
theorem EqPrefixSpecializationAt.saturated_empty_supply_cut_eq_or_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' [α,a,M,minor,b] pre σ [])
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (HH : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ historyTarget historyMap
      Γ Λ σ blocks Ξ χ plug chosen depth)
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HT : TypedSource (proofEraseCtx Λ) source)
    (RP : ScopedComputeCount (PiInertStage D n) cp (proofEraseCtx Λ) source
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)))
    (HR : PiInertStage D n (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)) target)
    (HN : ¬ LevelPrimitive univs
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)) target)
    (RT : ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Λ) target endpoint)
    (HK : PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ) K endpoint ck)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU))
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j
      (proofEraseCtx Λ) source tail → K tail k → cost ≤ j+k) :
    env.IsDefEq univs Δ a b α ∨ ∃ u rawA,
      target = .lam rawA (.app
        ((ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)).liftN 1) (etaArgument u)) ∧
    ∃ A A' body' cd cb m,
      env.HasType univs Λ A (.sort u) ∧ proofErase Λ A = rawA ∧
      EqFrameInsertionChain Γ Γ' ρ τ (A :: Λ) (A.subst κ :: Λ') κ.lift υ.lift (blocks ++ [(1,0)]) ∧
      EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ historyTarget historyMap
        Γ (A :: Λ) σ (blocks ++ [(1,0)]) (A'.subst χ :: Ξ) χ.lift
        (fun e => plug (.lam A' e)) chosen (depth+1) ∧
      endpoint = .lam A' body' ∧
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ) (proofErase Λ A) A' ∧
      TypedSource (proofEraseCtx (A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
            (extra.map (·.liftN 1) ++ [etaArgument u]))) ∧
      ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
            (extra.map (·.liftN 1) ++ [etaArgument u]))) body' ∧
      PiInertTypedContinuationRun D Ω out (proofEraseCtx (A :: Λ))
        (fun body k => K (.lam A' body) k) body' ck ∧ cb+ck < cost ∧
      (∀ later j body k, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx (A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
            (extra.map (·.liftN 1) ++ [etaArgument u]))) body →
        K (.lam A' body) k → cb+ck ≤ j+k) ∧
      EqChainContinuationMinimum D Δ v w [α,a,M,minor,b] Ω out (cb+ck) ∧
      ((∃ v'' w'' pre' extra',
        body' = ProofShape.mkApps (.const ``Eq.rec [v'',w''])
          (((pre'.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++ extra') ∧
        EqPrefixSpecializationAt Γ Δ v w v'' w'' [α,a,M,minor,b] pre' σ [] ∧
        env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
          (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F ∧
        List.Forall₂ (· ≈ ·) [v',w'] [v'',w''] ∧
        List.Forall₂ (ScopedCompute (PiInertStage D m) (proofEraseCtx (A :: Λ)))
          (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
            (extra.map (·.liftN 1) ++ [etaArgument u]))
          (((pre'.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++ extra') ∧
        List.Forall₂ (ScopedCompute (PiInertStage D m) (proofEraseCtx (A :: Λ)))
          (extra.map (·.liftN 1) ++ [etaArgument u]) extra') ∨
      ChosenEqChainSpineCut D Γ Δ (A :: Λ) (blocks ++ [(1,0)]) v w [α,a,M,minor,b] σ [] m
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
            (extra.map (·.liftN 1) ++ [etaArgument u]))) body' cb) := by
  have HP := (H.saturated_chain_completion W J hf hn extra).embedding
  rcases HP.hole_cut_eq_or_smaller heq hs hreg hoff hRec hΔ ht (C := .hole)
      .hole HT RP HR HN RT HK HE HO hcost HM with
    Hlower | ⟨k, rawA, rawB, u, rfl, _, RN, SD, _, _, _⟩
  · exact .inl Hlower
  · have HHnext := H.saturated_empty_supply_eta_history heq hs
      (erased_static_structure_eta_expansion_stage_certificate_descent heq hs k) hΔ W J HH hf hn HT
      RN SD RP HR RT HK hcost HM
    exact .inr ⟨u, rawA, rfl, HHnext⟩

end Lean4Lean.VEnv.Strengthening
