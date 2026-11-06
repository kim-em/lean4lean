import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqChainAnnotations

/-! # Match computed retained annotations on both sides of a paired chain

A retained endpoint computes its source annotation before lifting its old map.
The outgoing domain is the computed annotation's actual substituted image.
The source binder and both chosen target images remain unchanged.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

private theorem typed_map_target_convert
    (S : Ctx.SubstEq env univs Γ' ρ ρ Γ)
    (C : IsDefEqCtx env univs [] Γ' Γ₁') : Ctx.SubstEq env univs Γ₁' ρ ρ Γ := by
  apply substEq_of_lookup S.wf
  intro i A hl
  exact (S.lookup hl).hasType.1.defeqDFC henv C

private theorem erased_map_target_convert
    (S : Ctx.SubstEq env univs Γ' ρ ρ Γ)
    (C : IsDefEqCtx env univs [] Γ' Γ₁')
    (E : ErasedSubstAgreement Γ Γ' ρ τ) : ErasedSubstAgreement Γ Γ₁' ρ τ := by
  intro i A hl hn
  exact (proofErase_defeqCtx C.isType C (S.lookup hl).hasType.1).symm.trans (E hl hn)

/-- Convert the outgoing context of a paired frame. Both chosen assignments
and the literal actual/raw maps are kept, including the old agreement proof. -/
theorem EqSpecializationFrame.target_convert
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (C : IsDefEqCtx env univs [] Γ' Γ₁') :
    EqSpecializationFrame Γ Γ₁' Δ σ σ' ρ τ :=
  ⟨substEq_source_convert hΔ C W.target, typed_map_target_convert W.actual C,
    erased_map_target_convert W.actual C W.erase, W.agree⟩

/-- Actual definitional equality weakens through the same recorded source
insertions as typing; this is used only for annotation conversion. -/
theorem EqFrameInsertionChain.weak_eq
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (HE : env.IsDefEq univs Γ A B T) :
    env.IsDefEq univs Λ (blocks.actual A) (blocks.actual B) (blocks.actual T) := by
  induction J with
  | refl => exact HE
  | step J I ih => simpa only [EqInsertionPath.actual_snoc] using ih.weakN henv I.source

/-- Lift one insertion beneath a retained source domain and a definitionally
equal outgoing domain. The outgoing domain is the new lower domain's actual
image. Source and target insertions have the same shifted count/offset, and
both syntactic commuting equations are unchanged. -/
theorem EqFrameInsertion.under_binder_converted
    (I : EqFrameInsertion Γ Γ' Λ Λ' count offset ρ τ κ υ)
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (S : Ctx.SubstEq env univs Γ' ρ ρ Γ)
    (HAB : env.IsDefEq univs Γ A B (.sort u)) :
    EqFrameInsertion (A :: Γ) (B.subst ρ :: Γ')
      (A.liftN count offset :: Λ) ((B.subst ρ).liftN count offset :: Λ')
      count (offset+1) ρ.lift τ.lift κ.lift υ.lift := by
  have IB := I.under_binder_actual hΓ' S HAB.hasType.1
  have HB := (HAB.subst henv.orderedStrong S hΓ').weakN henv I.target
  have C : IsDefEqCtx env univs []
      ((A.subst ρ).liftN count offset :: Λ') ((B.subst ρ).liftN count offset :: Λ') :=
    .succ (.refl I.target_wf) HB
  refine ⟨IB.source, I.target.succ, (C.symm henv.ordered).isType,
    typed_map_target_convert IB.actual C, ?_, IB.semantic, IB.erased⟩
  intro i T hl hn
  exact erased_map_target_convert IB.actual C IB.erase hl hn

/-- The full insertion chain lifts beneath a retained source annotation and
its computed outgoing image. It keeps the actual maps and original source
binder, while every outgoing domain and block is matched to the new annotation. -/
theorem EqFrameInsertionChain.under_binder_converted
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (HAB : env.IsDefEq univs Γ A B (.sort u)) :
    EqFrameInsertionChain (A :: Γ) (B.subst ρ :: Γ') ρ.lift τ.lift
      (blocks.actual A :: Λ) (blocks.actual (B.subst ρ) :: Λ')
      κ.lift υ.lift blocks.underBinder := by
  induction J with
  | refl => exact .refl
  | @step Λ Λ' κ υ blocks Ψ Ψ' n k χ ω J I ih =>
    obtain ⟨hΛ', S, _⟩ := J.actual W
    have HB : env.IsDefEq univs Λ (blocks.actual A) (blocks.actual B) (.sort u) := by
      simpa only [EqInsertionPath.actual_sort] using J.weak_eq HAB
    have IN := I.under_binder_converted hΛ' S HB
    rw [J.semantic B] at IN
    have H := ih.step IN
    simpa only [EqInsertionPath.underBinder, List.map_append, List.map_cons, List.map_nil,
      EqInsertionPath.actual_snoc] using H

/-- Realize the actual retained-binder endpoint, including its changed
outgoing annotation. Native domain computation descends through the chain;
its new outgoing raw domain is exactly the recorded result substituted by the
old upper map. The source binder and both chosen images are preserved. -/
theorem EqFrameInsertionChain.retained_endpoint
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hA : env.HasType univs Γ A (.sort u))
    (hy : env.HasType univs Δ y (A.subst σ))
    (HC : PiInertEndpointContext D (proofEraseCtx Λ) (proofEraseCtx Λ') υ)
    (RD : ScopedCompute (PiInertStage D n) (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ A)) rawA') :
    ∃ B, env.IsDefEq univs Γ A B (.sort u) ∧
      ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ B) ∧
      blocks.erased (proofErase Γ B) = rawA' ∧
      EqSpecializationFrame (A :: Γ) (B.subst ρ :: Γ') Δ
        (σ.cons y) (σ'.cons y) ρ.lift τ.lift ∧
      EqFrameInsertionChain (A :: Γ) (B.subst ρ :: Γ') ρ.lift τ.lift
        (blocks.actual A :: Λ) (blocks.actual (B.subst ρ) :: Λ')
        κ.lift υ.lift blocks.underBinder ∧
      proofErase Λ' (blocks.actual (B.subst ρ)) = rawA'.subst υ ∧
      PiInertEndpointContext D (proofEraseCtx (blocks.actual A :: Λ))
        (proofEraseCtx (blocks.actual (B.subst ρ) :: Λ')) υ.lift := by
  obtain ⟨B, HAB, RB, EB⟩ :=
    J.compute_certificate (pi_inert_stage_certificate_descent heq hs n) W hA RD
  have C : IsDefEqCtx env univs [] (A.subst ρ :: Γ') (B.subst ρ :: Γ') :=
    .succ (.refl W.target.wf) (HAB.subst henv.orderedStrong W.actual W.target.wf)
  have WF := (W.under_binder hΔ hA hy).target_convert hΔ C
  have JF := J.under_binder_converted W HAB
  obtain ⟨hΛ', S, ES⟩ := J.actual W
  have Eout : proofErase Λ' (blocks.actual (B.subst ρ)) = rawA'.subst υ := by
    rw [← J.semantic B]
    exact (proofErase_subst_with hΛ' S (J.weak HAB.hasType.2) ES).trans
      (congrArg (·.subst υ) ((J.erase_actual W HAB.hasType.2).trans EB))
  refine ⟨B, HAB, RB, EB, WF, JF, Eout, ?_⟩
  simpa only [proofEraseCtx, J.erase_actual W hA, Eout] using
    PiInertEndpointContext.binder RD HC

/-- A chosen body specialization survives the actual retained endpoint with
its changed outgoing annotation. The result retains the same chosen source
and outgoing images, the shifted entire chain, and exact upper raw endpoint
agreement. The native annotation path is used only at its actual source. -/
theorem EqPrefixSpecializationAt.retained_chain_endpoint
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original pre (σ.cons y) pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (HC : PiInertEndpointContext D (proofEraseCtx Λ) (proofEraseCtx Λ') υ)
    (RD : ScopedCompute (PiInertStage D n) (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ A)) rawA') :
    ∃ B, env.IsDefEq univs Γ A B (.sort u) ∧
      blocks.erased (proofErase Γ B) = rawA' ∧
      EqSpecializationFrame (A :: Γ) (B.subst ρ :: Γ') Δ
        (σ.cons y) (σ'.cons y) ρ.lift τ.lift ∧
      EqFrameInsertionChain (A :: Γ) (B.subst ρ :: Γ') ρ.lift τ.lift
        (blocks.actual A :: Λ) (blocks.actual (B.subst ρ) :: Λ')
        κ.lift υ.lift blocks.underBinder ∧
      PiInertEndpointContext D (proofEraseCtx (blocks.actual A :: Λ))
        (proofEraseCtx (blocks.actual (B.subst ρ) :: Λ')) υ.lift ∧
      proofErase Λ' (blocks.actual (B.subst ρ)) = rawA'.subst υ ∧
      EqPrefixSpecializationAt (B.subst ρ :: Γ') Δ v w v' w' original
        (pre.map (·.subst ρ.lift)) (σ'.cons y) pending ∧
      env.HasType univs (B.subst ρ :: Γ')
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map (·.subst ρ.lift))) (F.subst ρ.lift) ∧
      (((pre.map (·.subst ρ.lift)).map (proofErase (B.subst ρ :: Γ'))).map blocks.underBinder.erased) =
        (((pre.map (proofErase (A :: Γ))).map blocks.underBinder.erased).map (·.subst υ.lift)) := by
  have hy : env.HasType univs Δ y (A.subst σ) := by
    have HS := H.1
    cases HS with
    | cons _ _ hy => exact hy.hasType.1
  obtain ⟨B, HAB, _, EB, WF, JF, Eout, HCout⟩ := J.retained_endpoint heq hs hΔ W hA hy HC RD
  obtain ⟨Hout, hout, Epre⟩ := H.frame hΔ WF hf
  refine ⟨B, HAB, EB, WF, JF, HCout, Eout, Hout, hout, ?_⟩
  rw [Epre]
  simp only [List.map_map, Function.comp_def, JF.erased]

/-- Insert an unused source domain while using its converted image on the
outgoing side. The original lower assignments need no image for this binder;
the actual upper map lifts and the old chain receives one top block. -/
theorem EqFrameInsertionChain.insert_converted_domain
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (HAB : env.IsDefEq univs Λ A B (.sort u)) :
    EqFrameInsertionChain Γ Γ' ρ τ (A :: Λ) (B.subst κ :: Λ')
      κ.lift υ.lift (blocks ++ [(1,0)]) := by
  obtain ⟨hΛ', S, ES⟩ := J.actual W
  have SF := S.lift henv.ordered HAB.hasType.1
  have C : IsDefEqCtx env univs [] (A.subst κ :: Λ') (B.subst κ :: Λ') :=
    .succ (.refl hΛ') (HAB.subst henv.orderedStrong S hΛ')
  apply J.step
  refine ⟨Ctx.LiftN.one, Ctx.LiftN.one, (C.symm henv.ordered).isType,
    typed_map_target_convert SF C, ?_, ?_, ?_⟩
  · intro i T hl hn
    exact erased_map_target_convert SF C (ErasedSubstAgreement.lift hΛ' S HAB.hasType.1 ES) hl hn
  · intro e; exact VExpr.lift_subst_lift
  · intro e; exact ProofShape.lift_subst_lift e υ

/-- Match an actual retained endpoint when its new binder is unused by the
chosen lower prefix. Its domain may depend on any older upper binder. Native
annotation computation is realized in that actual upper scope, and the new
outgoing annotation is exactly its image under the actual old map. No target
inhabitant or proposition restriction is required. -/
theorem EqFrameInsertionChain.retained_unused_endpoint
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hA : env.HasType univs Λ A (.sort u))
    (HC : PiInertEndpointContext D (proofEraseCtx Λ) (proofEraseCtx Λ') υ)
    (RD : ScopedCompute (PiInertStage D n) (proofEraseCtx Λ) (proofErase Λ A) rawA') :
    ∃ B, env.IsDefEq univs Λ A B (.sort u) ∧ proofErase Λ B = rawA' ∧
      EqFrameInsertionChain Γ Γ' ρ τ (A :: Λ) (B.subst κ :: Λ')
        κ.lift υ.lift (blocks ++ [(1,0)]) ∧
      proofErase Λ' (B.subst κ) = rawA'.subst υ ∧
      PiInertEndpointContext D (proofEraseCtx (A :: Λ))
        (proofEraseCtx (B.subst κ :: Λ')) υ.lift := by
  obtain ⟨hΛ', S, ES⟩ := J.actual W
  obtain ⟨B, HAB, EB⟩ := proofErase_scoped_compute_realize
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
    S.wf hA rfl rfl RD
  have Eout : proofErase Λ' (B.subst κ) = rawA'.subst υ :=
    (proofErase_subst_with hΛ' S HAB.hasType.2 ES).trans (congrArg (·.subst υ) EB)
  refine ⟨B, HAB, EB, J.insert_converted_domain W HAB, Eout, ?_⟩
  simpa only [proofEraseCtx, Eout] using PiInertEndpointContext.binder RD HC

end Lean4Lean.VEnv.Strengthening
