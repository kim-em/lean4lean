import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedTelescopeSupply

/-! # Supplied scope changes between different insertion paths

The lower agreeing map and upper typed map commute with separate source and
outgoing insertion paths. Retained chosen binders lift both maps; unused
insertions lift only the upper map. Both kinds may have computed annotations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation

/-- The actual instantiation square uses a shifted incoming insertion path. -/
theorem EqInsertionPath.actual_inst (blocks : EqInsertionPath) (body x : VExpr) :
    blocks.actual (body.inst x) = (blocks.underBinder.actual body).inst (blocks.actual x) := by
  induction blocks generalizing body x with
  | nil => rfl
  | cons p blocks ih =>
    obtain ⟨n,k⟩ := p
    change EqInsertionPath.actual blocks ((body.inst x).liftN n k) = _
    rw [VExpr.liftN_inst_hi]
    exact ih (body.liftN n (k+1)) (x.liftN n k)

/-- Actual insertion commutes with a lambda and shifts its body path. -/
theorem EqInsertionPath.actual_lam (blocks : EqInsertionPath) (A body : VExpr) :
    blocks.actual (.lam A body) = .lam (blocks.actual A) (blocks.underBinder.actual body) := by
  induction blocks generalizing A body with
  | nil => rfl
  | cons p blocks ih =>
    obtain ⟨n,k⟩ := p
    simpa only [EqInsertionPath.actual, VExpr.liftN,
      EqInsertionPath.underBinder, List.map_cons] using ih (A.liftN n k) (body.liftN n (k+1))

variable [Params]
open private typed_map_target_convert erased_map_target_convert
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqChainRetained

/-- An agreeing lower scope change and its actual upper realization, with
separate insertion paths. The upper typed map is retained because later
inserted domains may depend on any upper binder and have no lower image. -/
structure EqSupplyInsertionSquare (Γ Γ' Δ : List VExpr) (σ σ' ρ : VExpr.Subst)
    (τ : ProofShape.Subst) (Λ Λ' : List VExpr) (κ : VExpr.Subst) (υ : ProofShape.Subst)
    (incoming outgoing : EqInsertionPath) : Prop where
  lower : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ
  source : EqFrameInsertionChain Γ Γ VExpr.Subst.id ProofShape.Subst.id
    Λ Λ VExpr.Subst.id ProofShape.Subst.id incoming
  target : EqFrameInsertionChain Γ' Γ' VExpr.Subst.id ProofShape.Subst.id
    Λ' Λ' VExpr.Subst.id ProofShape.Subst.id outgoing
  target_wf : OnCtx Λ' (env.IsType univs)
  actual : Ctx.SubstEq env univs Λ' κ κ Λ
  erase : ErasedSubstAgreement Λ Λ' κ υ
  semantic : ∀ e : VExpr, (incoming.actual e).subst κ = outgoing.actual (e.subst ρ)
  erased : ∀ e : ProofShape, (incoming.erased e).subst υ = outgoing.erased (e.subst τ)

/-- A computed actual older argument creates the square, with one fewer
binder on the outgoing side. Agreement comes from its original chosen image;
the actual upper argument and both insertion paths remain explicit. -/
theorem EqSupplyInsertionSquare.supplied
    (harg : ErasedScopedPrimitiveCertificateDescent ArgStep ArgStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x A)
    (RX : ScopedCompute ArgStep (proofEraseCtx Λ) (blocks.erased (proofErase Γ x)) rawX) :
    ∃ x', env.IsDefEq univs Γ x x' A ∧ blocks.erased (proofErase Γ x') = rawX ∧
      EqSupplyInsertionSquare (A :: Γ) Γ Δ (σ.cons (x.subst σ)) σ
        (VExpr.Subst.one x') (ProofShape.Subst.one (proofErase Γ x'))
        (blocks.actual A :: Λ) Λ (VExpr.Subst.one (blocks.actual x'))
        (ProofShape.Subst.one rawX) blocks.underBinder blocks := by
  obtain ⟨x', HX, _, EX⟩ := J.compute_certificate harg W hx RX
  have WI := EqSpecializationFrame.inst W.agree.left hA HX.hasType.2
    (HX.subst henv.orderedStrong W.agree.left hΔ)
  have W₀ := EqSpecializationFrame.of_conversion hΔ W.agree.left (.refl W.actual.wf)
  have JS := J.source_identity.under_binder W₀ hA
  have hΛ := (J.actual W).2.1.wf
  have hAup : env.HasType univs Λ (blocks.actual A) (.sort u) := by
    simpa only [EqInsertionPath.actual_sort] using J.weak hA
  have hΛA : OnCtx (blocks.actual A :: Λ) (env.IsType univs) := ⟨hΛ, u, hAup⟩
  have EXup := (J.erase_actual W HX.hasType.2).trans EX
  refine ⟨x', HX, EX, WI, ?_, J.source_identity, hΛ,
    Ctx.InstN.zero.substEq hΛA (J.weak HX.hasType.2), ?_, ?_, ?_⟩
  · simpa only [VExpr.id_lift, ProofShape.Subst.id_lift, VExpr.subst_id] using JS
  · intro i T hl hn
    simpa only [EXup] using erasedSubstAgreement_one hΛA (J.weak HX.hasType.2) hl hn
  · intro e
    simpa only [VExpr.inst_eq] using (blocks.actual_inst e x').symm
  · intro e
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, EX] using
      (blocks.erased_inst e (proofErase Γ x')).symm

/-- Extend the square under a chosen retained binder after lowering its
actual annotation computation. Both maps lift and both paths shift; the new
chosen image is preserved using the old lower agreement. -/
theorem EqSupplyInsertionSquare.retained
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (Q : EqSupplyInsertionSquare Γ Γ' Δ σ σ' ρ τ Λ Λ' κ υ incoming outgoing)
    (hA : env.HasType univs Γ A (.sort u))
    (hy : env.HasType univs Δ y (A.subst σ))
    (RD : ScopedCompute (PiInertStage D n) (proofEraseCtx Λ)
      (incoming.erased (proofErase Γ A)) rawA') :
    ∃ B, env.IsDefEq univs Γ A B (.sort u) ∧ incoming.erased (proofErase Γ B) = rawA' ∧
      EqSupplyInsertionSquare (A :: Γ) (B.subst ρ :: Γ') Δ (σ.cons y) (σ'.cons y)
        ρ.lift τ.lift (incoming.actual A :: Λ) (outgoing.actual (B.subst ρ) :: Λ')
        κ.lift υ.lift incoming.underBinder outgoing.underBinder ∧
      proofErase Λ' (outgoing.actual (B.subst ρ)) = rawA'.subst υ := by
  have WS := EqSpecializationFrame.of_conversion hΔ Q.lower.agree.left (.refl Q.lower.actual.wf)
  have WT := EqSpecializationFrame.of_conversion hΔ Q.lower.target (.refl Q.lower.target.wf)
  obtain ⟨B, HAB, _, EB⟩ := Q.source.compute_certificate
    (pi_inert_stage_certificate_descent heq hs n) WS hA RD
  have C : IsDefEqCtx env univs [] (A.subst ρ :: Γ') (B.subst ρ :: Γ') :=
    .succ (.refl Q.lower.target.wf) (HAB.subst henv.orderedStrong Q.lower.actual Q.lower.target.wf)
  have WF := (Q.lower.under_binder hΔ hA hy).target_convert hΔ C
  have hBout : env.HasType univs Γ' (B.subst ρ) (.sort u) := by
    simpa only [VExpr.subst] using HAB.hasType.2.subst henv.orderedStrong Q.lower.actual Q.lower.target.wf
  have hAup : env.HasType univs Λ (incoming.actual A) (.sort u) := by
    simpa only [EqInsertionPath.actual_sort] using Q.source.weak hA
  have HEup := (Q.source.weak_eq HAB).subst henv.orderedStrong Q.actual Q.target_wf
  have CU : IsDefEqCtx env univs []
      ((incoming.actual A).subst κ :: Λ') (outgoing.actual (B.subst ρ) :: Λ') := by
    apply IsDefEqCtx.succ (.refl Q.target_wf)
    simpa only [EqInsertionPath.actual_sort, VExpr.subst, Q.semantic] using HEup
  have EU : proofErase Λ' (outgoing.actual (B.subst ρ)) = rawA'.subst υ := by
    rw [← Q.semantic B]
    exact (proofErase_subst_with Q.target_wf Q.actual (Q.source.weak HAB.hasType.2) Q.erase).trans
      (congrArg (·.subst υ) ((Q.source.erase_actual WS HAB.hasType.2).trans EB))
  refine ⟨B, HAB, EB, ⟨WF, ?_, ?_, (CU.symm henv.ordered).isType,
    typed_map_target_convert (Q.actual.lift henv.ordered hAup) CU, ?_, ?_, ?_⟩, EU⟩
  · simpa only [VExpr.id_lift, ProofShape.Subst.id_lift, VExpr.subst_id] using Q.source.under_binder WS hA
  · simpa only [VExpr.id_lift, ProofShape.Subst.id_lift, VExpr.subst_id] using Q.target.under_binder WT hBout
  · intro i T hl hn
    exact erased_map_target_convert (Q.actual.lift henv.ordered hAup) CU
      (ErasedSubstAgreement.lift Q.target_wf Q.actual hAup Q.erase) hl hn
  · intro e
    have HE := Q.semantic (.lam (.sort .zero) e)
    simp only [EqInsertionPath.actual_lam, VExpr.subst] at HE
    exact (VExpr.lam.inj HE).2
  · intro e
    exact (EqInsertionPath.square_under_binder (fun e => (Q.erased e).symm) e).symm

/-- Insert an unused actual binder with a computed annotation. Its domain
may depend on any upper variable. Only the upper map lifts; both lower chosen
assignments stay fixed, and neither requires an inhabitant of the new type. -/
theorem EqSupplyInsertionSquare.unused
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (Q : EqSupplyInsertionSquare Γ Γ' Δ σ σ' ρ τ Λ Λ' κ υ incoming outgoing)
    (hA : env.HasType univs Λ A (.sort u))
    (RD : ScopedCompute (PiInertStage D n) (proofEraseCtx Λ) (proofErase Λ A) rawA') :
    ∃ B, env.IsDefEq univs Λ A B (.sort u) ∧ proofErase Λ B = rawA' ∧
      EqSupplyInsertionSquare Γ Γ' Δ σ σ' ρ τ (A :: Λ) (B.subst κ :: Λ')
        κ.lift υ.lift (incoming ++ [(1,0)]) (outgoing ++ [(1,0)]) ∧
      proofErase Λ' (B.subst κ) = rawA'.subst υ := by
  obtain ⟨B, HAB, EB⟩ := proofErase_scoped_compute_realize
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
    Q.actual.wf hA rfl rfl RD
  have WS := EqSpecializationFrame.of_conversion hΔ Q.lower.agree.left (.refl Q.lower.actual.wf)
  have WT := EqSpecializationFrame.of_conversion hΔ Q.lower.target (.refl Q.lower.target.wf)
  have hBout : env.HasType univs Λ' (B.subst κ) (.sort u) := by
    simpa only [VExpr.subst] using HAB.hasType.2.subst henv.orderedStrong Q.actual Q.target_wf
  have CU : IsDefEqCtx env univs [] (A.subst κ :: Λ') (B.subst κ :: Λ') :=
    .succ (.refl Q.target_wf) (HAB.subst henv.orderedStrong Q.actual Q.target_wf)
  refine ⟨B, HAB, EB, ⟨Q.lower, ?_, ?_, (CU.symm henv.ordered).isType,
    typed_map_target_convert (Q.actual.lift henv.ordered hA) CU, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [VExpr.subst_id, VExpr.id_lift, ProofShape.Subst.id_lift] using Q.source.insert_domain WS hA
  · simpa only [VExpr.subst_id, VExpr.id_lift, ProofShape.Subst.id_lift] using Q.target.insert_domain WT hBout
  · intro i T hl hn
    exact erased_map_target_convert (Q.actual.lift henv.ordered hA) CU
      (ErasedSubstAgreement.lift Q.target_wf Q.actual hA Q.erase) hl hn
  · intro e
    simpa only [EqInsertionPath.actual_snoc, VExpr.lift_subst_lift] using
      congrArg (·.liftN 1) (Q.semantic e)
  · intro e
    simpa only [EqInsertionPath.erased_snoc, ProofShape.lift_subst_lift] using
      congrArg (·.liftN 1) (Q.erased e)
  · exact (proofErase_subst_with Q.target_wf Q.actual HAB.hasType.2 Q.erase).trans
      (congrArg (·.subst υ) EB)

end Lean4Lean.VEnv.Strengthening
