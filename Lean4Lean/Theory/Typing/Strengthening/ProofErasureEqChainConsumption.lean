import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSaturatedChain
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqConsumedArgument

/-! # Actual consumption of a saturated chain's unused top binder

Descend component certificates before consuming the actual endpoint argument.
The completed chosen prefix ignores the new binder, while extra arguments keep
their exact instantiated syntax. The original paired frame and older insertion
chain therefore survive without assigning a target inhabitant to the new domain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Consume the actual interpreted top binder after arbitrary component
computation of a saturated spine. Both chosen lower assignments and the older
insertion chain are kept. The actual argument is realized at its displayed
domain, but requires no target image: every tracked component descends below
the consumed binder. The full raw endpoint and its outgoing image retain all
extra arguments, including their actual dependence on the consumed argument. -/
theorem EqPrefixSpecializationAt.saturated_chain_consumed_components
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ [])
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (hA : env.HasType univs Λ A (.sort u))
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx (A :: Λ)))
      (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++ extra) raw)
    (WX : ContextSubstitution (proofEraseCtx (A :: Λ)) (proofEraseCtx Λ)
      (ProofShape.Subst.one rawX)) :
    ∃ pre' x, env.HasType univs Λ x A ∧
      ErasedSubstAgreement (A :: Λ) Λ (VExpr.Subst.one x) (ProofShape.Subst.one rawX) ∧
      EqPrefixSpecializationAt Γ Δ v w v'' w'' original pre' σ [] ∧
      EqPrefixSpecializationAt Γ' Δ v w v'' w'' original (pre'.map (·.subst ρ)) σ' [] ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F ∧
      raw.map (·.inst rawX) = ((pre'.map (proofErase Γ)).map blocks.erased) ++
        (raw.drop pre.length).map (·.inst rawX) ∧
      (raw.map (·.inst rawX)).map (·.subst υ) =
        (((pre'.map (·.subst ρ)).map (proofErase Γ')).map blocks.erased) ++
          (raw.drop pre.length).map (fun e => (e.inst rawX).subst υ) ∧
      EqTargetPrefixCompletion Δ v w original (proofEraseCtx Λ)
        (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (raw.map (·.inst rawX))) := by
  obtain ⟨hΛ', S, _⟩ := J.actual W
  obtain ⟨x, hx, _, EX⟩ := WX.realize_one ⟨S.wf, u, hA⟩
  obtain ⟨pre', HP, Hout, _, Eraw, HE, _⟩ :=
    H.saturated_chain_components hstep hΔ W (J.insert_domain W hA) hf hn HC HA
  have EI : (raw.take pre.length).map (·.inst rawX) =
      (pre'.map (proofErase Γ)).map blocks.erased := by
    rw [← Eraw, List.map_map]
    simp only [Function.comp_def, EqInsertionPath.erased_snoc, ProofShape.inst_eq_subst,
      ProofShape.Subst.liftN, ProofShape.Subst.one, ProofShape.lift_subst_cons,
      ProofShape.subst_id]
  have Efull : raw.map (·.inst rawX) = ((pre'.map (proofErase Γ)).map blocks.erased) ++
      (raw.drop pre.length).map (·.inst rawX) := by
    rw [← EI, ← List.map_append, List.take_append_drop]
  have hn' := fun hp => hn ((isProof_congr H.1.wf HE).2 hp)
  have HPfull := HP.saturated_chain_completion W J HE.hasType.2 hn'
    ((raw.drop pre.length).map (·.inst rawX))
  obtain ⟨_, _, Eout⟩ := HP.frame hΔ W HE.hasType.2
  refine ⟨pre', x, hx, EX, HP, Hout, HE, Efull, ?_, Efull.symm ▸ HPfull⟩
  rw [Efull, List.map_append, Eout]
  simp only [List.map_map, Function.comp_def, J.erased]

/-- The actual application after consuming a saturated unused binder keeps
its selected suffix and removes one continuation frame. Component descent
supplies completion at that exact consumed endpoint even for a nonproof domain.
The original lower assignments remain available for subsequent steps. Primitive
cost decreases when the preceding path is nonempty; otherwise the recorded
frame count decreases. No unrestricted refocusing is used. -/
theorem EqPrefixSpecializationAt.saturated_chain_application_progress
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ [])
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (hA : env.HasType univs Λ A (.sort u))
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx (A :: Λ)))
      (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++ extra) raw)
    (WX : ContextSubstitution (proofEraseCtx (A :: Λ)) (proofEraseCtx Λ)
      (ProofShape.Subst.one rawX))
    (HT : TypedSource (proofEraseCtx (A :: Λ))
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) raw))
    (HTsource : TypedSource (proofEraseCtx (A :: Λ)) source)
    (RP : ScopedComputeCount (PiInertStage D n) cb (proofEraseCtx (A :: Λ)) source
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) raw))
    (HTnext : TypedSource (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (raw.map (·.inst rawX) ++ pending)))
    (RT : ScopedComputeCount (PiInertStage D m) cs (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (raw.map (·.inst rawX) ++ pending)) endpoint)
    (HK : PiInertRunFrames D Ω out (proofEraseCtx Λ) K endpoint ck frames)
    (hc : cb+(cs+ck) = cost)
    (HM : ∀ later j tail k,
      ScopedComputeCount (PiInertStage D later) j (proofEraseCtx (A :: Λ)) source tail →
      PiInertApplicationContinuation D (proofEraseCtx Λ) (ProofShape.Subst.one rawX) pending K tail k →
      cost ≤ j+k) :
    ∃ pre', EqPrefixSpecializationAt Γ Δ v w v'' w'' original pre' σ [] ∧
      EqPrefixSpecializationAt Γ' Δ v w v'' w'' original (pre'.map (·.subst ρ)) σ' [] ∧
      raw.map (·.inst rawX) = ((pre'.map (proofErase Γ)).map blocks.erased) ++
        (raw.drop pre.length).map (·.inst rawX) ∧
      PiInertFrameMinimum D Ω out (proofEraseCtx (A :: Λ)) source cost (frames+1) ∧
      EqTargetPrefixCompletion Δ v w original (proofEraseCtx Λ)
        (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (raw.map (·.inst rawX) ++ pending)) ∧
      PiInertFrameMinimum D Ω out (proofEraseCtx Λ)
        (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (raw.map (·.inst rawX) ++ pending)) (cs+ck) frames ∧
      (cs+ck < cost ∨ cs+ck = cost ∧ frames < frames+1) := by
  obtain ⟨pre', _, _, _, HP, Hout, _, Efull, _, HPfull⟩ :=
    H.saturated_chain_consumed_components hstep hΔ W J hf hn hA HC HA WX
  have hlen : original.length ≤ (raw.map (·.inst rawX)).length := by
    have HL := HP.2.2.length_eq
    have HR := congrArg List.length Efull
    simp only [List.length_append, List.length_map, List.length_nil, Nat.add_zero] at HL HR ⊢
    omega
  have EP : ProofShape.mkApps
      ((ProofShape.mkApps (.const ``Eq.rec [v'',w'']) raw).subst (ProofShape.Subst.one rawX)) pending =
      ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (raw.map (·.inst rawX) ++ pending) := by
    simp only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.mkApps_append,
      ProofShape.inst_eq_subst, ProofShape.Subst.liftN]
  have WX' : PiInertEndpointMap (proofEraseCtx (A :: Λ)) (proofEraseCtx Λ)
      (ProofShape.Subst.one rawX) := .inst WX
  refine ⟨pre', HP, Hout, Efull,
    ⟨PiInertApplicationContinuation D (proofEraseCtx Λ) (ProofShape.Subst.one rawX) pending K,
      n, cb, cs+ck, _, HTsource, RP,
      .application HT WX' (EP.symm ▸ HTnext) (EP.symm ▸ RT) HK, hc, HM⟩,
    HPfull.append_saturated hlen pending, ?_, by omega⟩
  refine ⟨K, m, cs, ck, endpoint, HTnext, RT, HK, rfl, ?_⟩
  intro later j tail k RJ HL
  have HB := HM n cb _ (j+k) RP ⟨later, j, tail, k, rfl, EP.symm ▸ RJ, HL⟩
  omega

end Lean4Lean.VEnv.Strengthening
