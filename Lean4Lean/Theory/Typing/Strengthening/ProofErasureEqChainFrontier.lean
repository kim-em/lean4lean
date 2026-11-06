import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqChainCut

/-! # A chosen paired-chain frontier from the original Eq probe

Strict induction exhausts actual non-level cuts while preserving chosen lower
assignments and insertion chains. The remaining component path retains its
actual continuation and next application. Agreement with a later consumed
used binder remains an obligation; it is not inferred from this frontier.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- The remaining actual component path, with a common chosen assignment and
paired chain at both endpoints. Its counted path, all-stage minimum and next
actual application are retained. The stored paired map is not asserted equal
to that next application's map without further ancestry evidence. -/
def EqChainComponentMinimum (D : Definitions) (Δ : List VExpr) (v w : VLevel)
    (original : List VExpr) (Ω : List ProofShape) (out : ProofShape) (budget : Nat) : Prop :=
  ∃ Γ Γ' Λ Λ' σ σ' ρ τ κ υ blocks v' w' v'' w'' pre pre' pending extra extra' F n cb ck K,
    cb+ck ≤ budget ∧
    EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending ∧
    EqPrefixSpecializationAt Γ Δ v w v'' w'' original pre' σ pending ∧
    EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ ∧
    EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks ∧
    env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F ∧
    ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) ∧
    env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
      (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F ∧
    (extra = [] ∨ pending = []) ∧ (extra' = [] ∨ pending = []) ∧
    TypedSource (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)) ∧
    ScopedComputeCount (PiInertStage D n) cb (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (((pre'.map (proofErase Γ)).map blocks.erased) ++ extra')) ∧
    List.Forall₂ (· ≈ ·) [v',w'] [v'',w''] ∧
    List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Λ))
      (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)
      (((pre'.map (proofErase Γ)).map blocks.erased) ++ extra') ∧
    PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ) K
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (((pre'.map (proofErase Γ)).map blocks.erased) ++ extra')) ck ∧
    (∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)) endpoint →
      K endpoint k → cb+ck ≤ j+k) ∧
    PiInertNextApplicationAtHole D Ω out (proofEraseCtx Λ) K
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (((pre'.map (proofErase Γ)).map blocks.erased) ++ extra')) ck

/-- A larger budget retains exactly the same component path and chosen data. -/
theorem EqChainComponentMinimum.mono
    (H : EqChainComponentMinimum D Δ v w original Ω out budget) (hb : budget ≤ larger) :
    EqChainComponentMinimum D Δ v w original Ω out larger := by
  obtain ⟨Γ, Γ', Λ, Λ', σ, σ', ρ, τ, κ, υ, blocks, v', w', v'', w'', pre, pre', pending,
    extra, extra', F, n, cb, ck, K, hc, H⟩ := H
  exact ⟨Γ, Γ', Λ, Λ', σ, σ', ρ, τ, κ, υ, blocks, v', w', v'', w'', pre, pre', pending,
    extra, extra', F, n, cb, ck, K, Nat.le_trans hc hb, H⟩

/-- Strong induction exhausts actual non-level cuts without forgetting the
chosen target assignment or insertion chain. The remaining current path is
component-only and retains its next actual application and unrestricted
competitor minimum. This does not resolve agreement for a new used-binder
consumption or prove that equal-cost continuation moves decrease. -/
theorem EqChainContinuationMinimum.component_frontier
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (HM : EqChainContinuationMinimum D Δ v w [α,a,M,minor,b] Ω out cost)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU)) :
    env.IsDefEq univs Δ a b α ∨ EqChainComponentMinimum D Δ v w [α,a,M,minor,b] Ω out cost := by
  induction cost using Nat.strongRecOn with
  | ind cost ih =>
    obtain ⟨Γ, Γ', Λ, Λ', σ, σ', ρ, τ, κ, υ, blocks, v', w', pre, pending, extra, F,
      HP, W, J, hf, hn, hextra, HM⟩ := HM
    obtain ⟨K, n, cb, ck, endpoint, HT, R, HK, hc, hmin⟩ := HM
    rcases HP.chain_counted_spine_or_cut heq hs hΔ W J hf hn hextra HT R with
      ⟨v'', w'', pre', extra', rfl, HPend, HEpre, HL, HA, _, hextra'⟩ | Hcut
    · refine .inr ⟨Γ, Γ', Λ, Λ', σ, σ', ρ, τ, κ, υ, blocks, v', w', v'', w'', pre, pre', pending,
        extra, extra', F, n, cb, ck, K, by omega, HP, HPend, W, J, hf, hn, HEpre,
        hextra, hextra', HT, R, HL, HA, HK, ?_, ?_⟩
      · simpa only [hc] using hmin
      · exact (HK.next_application HE
          (((RetainedConstHead.const (ls := [v'',w''])).mkApps _).eq_not_exposed heq)).substitution_hole
    · rcases Hcut.eq_or_smaller heq hs hreg hoff hRec hΔ ht W J HT HK HE HO
          (cost := cost) (by omega) hmin with Hlower | ⟨smaller, hsmall, HM'⟩
      · exact .inl Hlower
      · rcases ih smaller hsmall HM' with Hlower | HF
        · exact .inl Hlower
        · exact .inr (HF.mono (Nat.le_of_lt hsmall))

/-- The original lifted Eq probe reaches a component-only frontier retaining
chosen assignments and paired insertion history. No later-root completion or
frame-compatibility assumption is added. The original path is minimized over
all finite stages. Global continuation coverage and used-binder consumption
remain separate obligations, so this is a necessary frontier, not a sufficient
replacement for PropFront. -/
theorem pi_inert_eq_exposure_eq_or_chain_frontier
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w α a M minor b))
    (Eargs : args = (([α,a,M,minor,b].map (proofErase Γ)).map (·.liftN count offset)) ++ [.proof])
    (HT : ControlTyping (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) (.sort u))
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out) (HE : CarrierExposure out) :
    env.IsDefEq univs Γ a b α ∨ ∃ stage cost,
      ScopedComputeCount (PiInertStage D stage) cost (proofEraseCtx Γ')
        (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out ∧
      (∀ later j, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ')
        (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out → cost ≤ j) ∧
      EqChainComponentMinimum D Γ v w [α,a,M,minor,b] (proofEraseCtx Γ') out cost := by
  have HTsource : TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) := by
    obtain ⟨Ξ, e, hΞ, EΞ, he, Ee⟩ := HT
    exact ⟨Ξ, e, _, hΞ, EΞ, he, Ee⟩
  have HO := HT.compute
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)) R
  obtain ⟨initial, RC₀⟩ := R.count
  obtain ⟨stage, cost, RC, hmin⟩ := RC₀.minimal_across_stages
  have HM : PiInertTypedContinuationMinimum D (proofEraseCtx Γ') out (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) cost := by
    refine ⟨(fun e k => e = out ∧ k = 0), stage, cost, 0, out, HTsource, RC,
      .terminal (HTsource.pi_inert_compute heq hs RC.forget), by omega, ?_⟩
    rintro later j endpoint k RJ ⟨rfl, rfl⟩
    simpa only [Nat.add_zero] using hmin later j RJ
  obtain ⟨σ, pending, HP⟩ := EqPrefixSpecialization.of_typed hΓ ht
  have hp : pending = [] := by
    have HL := HP.2.2.length_eq
    simp only [List.length_append, List.length_map] at HL
    exact List.length_eq_zero_iff.mp (by omega)
  cases hp
  have WF := EqSpecializationFrame.of_conversion hΓ HP.1 (.refl hΓ)
  have I : EqFrameInsertion Γ Γ Γ' Γ' count offset
      VExpr.Subst.id ProofShape.Subst.id VExpr.Subst.id ProofShape.Subst.id := by
    refine ⟨W, W, hΓ', Ctx.SubstEq.id henv.ordered hΓ', ?_, ?_, ?_⟩
    · intro i A hl hnp
      simp only [VExpr.Subst.id, ProofShape.Subst.id, proofErase, if_neg hnp]
    · intro e; simp only [VExpr.subst_id]
    · intro e; simp only [ProofShape.subst_id]
  have J : EqFrameInsertionChain Γ Γ VExpr.Subst.id ProofShape.Subst.id Γ' Γ'
      VExpr.Subst.id ProofShape.Subst.id [(count,offset)] := EqFrameInsertionChain.refl.step I
  have HMchain : EqChainContinuationMinimum D Γ v w [α,a,M,minor,b] (proofEraseCtx Γ') out cost := by
    refine ⟨Γ, Γ, Γ', Γ', σ, σ, VExpr.Subst.id, ProofShape.Subst.id,
      VExpr.Subst.id, ProofShape.Subst.id, [(count,offset)], v, w, [α,a,M,minor,b], [], [.proof], T,
      HP, WF, J, ht, hn, .inr rfl, ?_⟩
    simpa only [Eargs, EqInsertionPath.erased] using HM
  rcases HMchain.component_frontier heq hs hreg hoff hRec hΓ ht HE HO with Hlower | HF
  · exact .inl Hlower
  · exact .inr ⟨stage, cost, RC, hmin, HF⟩

end Lean4Lean.VEnv.Strengthening
