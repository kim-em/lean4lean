import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqInsertionChain
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqFrameProgress

/-! # Saturated eta through a complete paired insertion chain

The tracked lower prefix is complete. Additional actual arguments remain in
the upper scope and need no target images. Native recovery types a new domain
in that actual upper scope, so its insertion can be appended to the old chain
even when the domain depends on earlier inserted binders or extra arguments.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- The chosen lower prefix supplies bounded completion after the exact
recorded insertion chain. The chosen assignment itself remains unchanged. -/
theorem EqPrefixSpecializationAt.chain_prefix_completion
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)) :
    EqTargetPrefixCompletion Δ v w original (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map blocks.erased)) := by
  have HPbase : EqHeadCompletion Δ v w original (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)) := by
    refine ⟨Γ, Γ, 0, 0, v', w', pre, F, H.1.wf, H.1.wf, Ctx.LiftN.zero [], rfl,
      hf, hn, H.forget, ?_⟩
    simp only [ProofShape.liftN_zero]
  have HP := EqTargetPrefixCompletion.of_completion (J.completion W hf (.base HPbase))
  simpa only [proofErase_const_spine H.1.wf hf hn, EqInsertionPath.erased_const_spine] using HP

/-- A fully completed lower prefix permits arbitrary actual extra arguments
above the insertion chain. Only the original prefix is tracked. -/
theorem EqPrefixSpecializationAt.saturated_chain_completion
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ [])
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (extra : List ProofShape) :
    EqTargetPrefixCompletion Δ v w original (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)) := by
  apply (H.chain_prefix_completion W J hf hn).append_saturated _ extra
  have HL := H.2.2.length_eq
  simpa only [List.length_map, List.length_append, List.length_nil, Nat.add_zero] using Nat.le_of_eq HL

/-- Component computation preserves the completed chosen prefix beneath the
entire insertion chain, while the remaining actual arguments stay in the
upper scope. The endpoint is the exact full raw vector, not just its tracked
prefix. Both lower and outgoing chosen assignments remain unchanged. -/
theorem EqPrefixSpecializationAt.saturated_chain_components
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ [])
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ))
      (((pre.map (proofErase Γ)).map blocks.erased) ++ extra) raw) :
    ∃ pre', EqPrefixSpecializationAt Γ Δ v w v'' w'' original pre' σ [] ∧
      EqPrefixSpecializationAt Γ' Δ v w v'' w'' original (pre'.map (·.subst ρ)) σ' [] ∧
      env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.subst ρ))) (F.subst ρ) ∧
      ((pre'.map (proofErase Γ)).map blocks.erased) = raw.take pre.length ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F ∧
      EqTargetPrefixCompletion Δ v w original (proofEraseCtx Λ)
        (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) raw) := by
  have HApre : List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ))
      ((pre.map (proofErase Γ)).map blocks.erased) (raw.take pre.length) := by
    have HH := Lean4Lean.List.forall₂_take HA ((pre.map (proofErase Γ)).map blocks.erased).length
    simp only [List.take_left] at HH
    simpa only [List.length_map] using HH
  obtain ⟨pre', HP, Hout, hout, Eraw, _, HE⟩ :=
    H.compute_insertion_chain hstep hΔ W J hf HC HApre
  have hn' := fun hp => hn ((isProof_congr H.1.wf HE).2 hp)
  have HPfull := HP.saturated_chain_completion W J HE.hasType.2 hn' (raw.drop pre.length)
  refine ⟨pre', HP, Hout, hout, Eraw, HE, ?_⟩
  simpa only [Eraw, List.take_append_drop] using HPfull

/-- Realize native recovery in the chain's actual upper source context, then
append the recovered domain as a new unused insertion. The old lower target
assignments are not extended. The domain may depend on any existing upper
binder; its outgoing image is supplied by the actual upper substitution. -/
theorem EqFrameInsertionChain.open_recovered_domain
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (HT : TypedSource (proofEraseCtx Λ) source)
    (RN : ScopedTypeRecovery Guard (proofEraseCtx Λ) source (.forallE rawA rawB))
    (SD : DomainSort (proofEraseCtx Λ) rawA u) :
    ∃ A, env.HasType univs Λ A (.sort u) ∧ proofErase Λ A = rawA ∧
      EqFrameInsertionChain Γ Γ' ρ τ (A :: Λ) (A.subst κ :: Λ') κ.lift υ.lift (blocks ++ [(1,0)]) := by
  have hΛ := (J.actual W).2.1.wf
  obtain ⟨Ξ, f, F, hΞ, EΞ, hf, Ef⟩ := HT
  have C := proofEraseCtx_defeq hΞ hΛ EΞ
  have hf' := hf.defeqDFC henv C
  have Ef' : proofErase Λ f = source := (proofErase_defeqCtx hΞ C hf).symm.trans Ef
  obtain ⟨A, B, hfPi, EA, _⟩ := proofErase_scoped_recovered_pi_descend
    hguard hΛ hΛ (Ctx.LiftN.zero []) hf'
    (by simpa only [List.length_nil, ProofShape.liftN_zero, Ef'] using RN)
  have EA : proofErase Λ A = rawA := by
    simpa only [List.length_nil, ProofShape.liftN_zero] using EA
  obtain ⟨_, hPi⟩ := hfPi.isType henv hΛ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  have SD' : DomainSort (proofEraseCtx Λ) ((proofErase Λ A).liftN 0) u := by
    simpa only [ProofShape.liftN_zero, EA] using SD
  have hA := SD'.descend hΛ hΛ (Ctx.LiftN.zero []) hA
  exact ⟨A, hA, EA, J.insert_domain W hA⟩

/-- Saturated eta appends a new insertion block while keeping the original
lower assignment, frame and completed prefix. Existing actual extra arguments
are lifted and the native fresh argument is appended. At arities beyond five
the new domain need not be a proposition; no such restriction is imposed. -/
theorem EqPrefixSpecializationAt.saturated_chain_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ [])
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HT : TypedSource (proofEraseCtx Λ) (ProofShape.mkApps (.const ``Eq.rec [v',w'])
      (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))
      (.forallE rawA rawB))
    (SD : DomainSort (proofEraseCtx Λ) rawA u) :
    ∃ A, env.HasType univs Λ A (.sort u) ∧ proofErase Λ A = rawA ∧
      EqFrameInsertionChain Γ Γ' ρ τ (A :: Λ) (A.subst κ :: Λ') κ.lift υ.lift (blocks ++ [(1,0)]) ∧
      EqTargetPrefixCompletion Δ v w original (proofEraseCtx (A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
            (extra.map (·.liftN 1) ++ [etaArgument u]))) := by
  obtain ⟨A, hA, EA, Jnew⟩ := J.open_recovered_domain
    (erased_static_structure_eta_expansion_stage_descent heq hs stage) W HT RN SD
  have HP := (H.saturated_chain_completion W J hf hn extra).eta heq hs hΔ ht RN SD
  refine ⟨A, hA, EA, Jnew, ?_⟩
  simpa only [proofEraseCtx, EA, ProofShape.liftN_mkApps, ProofShape.liftN, List.map_append,
    ProofShape.mkApps_append, ProofShape.mkApps, List.map_map, Function.comp_def,
    EqInsertionPath.erased_snoc] using HP

/-- A saturated actual cut, including any additional arguments beyond the
completed prefix, strictly descends under a newly recovered upper domain.
The whole insertion chain is retained and receives a new top block; the old
chosen lower assignment and frame do not change. This connects saturated
opening to the same unrestricted all-stage minimum used by short eta. -/
theorem EqPrefixSpecializationAt.saturated_chain_hole_cut_eq_or_smaller
    {C : ScopedHole Ξ (proofEraseCtx Λ)}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' [α,a,M,minor,b] pre σ [])
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : SpineBinderHole C) (HT : TypedSource Ξ source)
    (RP : ScopedComputeCount (PiInertStage D n) cp Ξ source
      (C.plug (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))))
    (HR : PiInertStage D n (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)) target)
    (HN : ¬ LevelPrimitive univs
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)) target)
    (RT : ScopedComputeCount (PiInertStage D n) ct Ξ (C.plug target) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Ξ K endpoint ck)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU))
    (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Ξ source tail →
      K tail k → cost ≤ j+k) :
    env.IsDefEq univs Δ a b α ∨ ∃ A u,
      env.HasType univs Λ A (.sort u) ∧ ct+ck < cost ∧
      EqFrameInsertionChain Γ Γ' ρ τ (A :: Λ) (A.subst κ :: Λ') κ.lift υ.lift (blocks ++ [(1,0)]) ∧
      target = .lam (proofErase Λ A)
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
            (extra.map (·.liftN 1) ++ [etaArgument u]))) ∧
      PiInertTypedContinuationMinimum D Ω out (proofEraseCtx (A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
            (extra.map (·.liftN 1) ++ [etaArgument u]))) (ct+ck) ∧
      EqTargetPrefixCompletion Δ v w [α,a,M,minor,b] (proofEraseCtx (A :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
            (extra.map (·.liftN 1) ++ [etaArgument u]))) := by
  have HP := (H.saturated_chain_completion W J hf hn extra).embedding
  rcases HP.hole_cut_eq_or_smaller heq hs hreg hoff hRec hΔ ht
      HC HT RP HR HN RT HK HE HO hcost hmin with
    Hlower | ⟨k, rawA, rawB, u, Etarget, _, RN, SD, hsmall, HM, _⟩
  · exact .inl Hlower
  · have HTroot := C.typed (HT.pi_inert_compute heq hs RP.forget)
    obtain ⟨A, hA, EA, Jnew, HPnew⟩ := H.saturated_chain_eta heq hs hΔ W J ht hf hn HTroot RN SD
    have ES : .app ((ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)).liftN 1) (etaArgument u) =
        ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++
            (extra.map (·.liftN 1) ++ [etaArgument u])) := by
      simp only [ProofShape.liftN_mkApps, ProofShape.liftN,
        ProofShape.mkApps_append, ProofShape.mkApps, List.map_map, Function.comp_def,
        EqInsertionPath.erased_snoc]
    exact .inr ⟨A, u, hA, hsmall, Jnew,
      by simpa only [EA, ES] using Etarget,
      by simpa only [proofEraseCtx, EA, ES] using HM, HPnew⟩

end Lean4Lean.VEnv.Strengthening
