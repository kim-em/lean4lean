import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqChainConsumption

/-! # Recorded annotation changes through paired insertion chains

Rebuild each source insertion over the lower realization chosen by recursive
certificate descent. Equal erased contexts justify this rebuilding. Outgoing
contexts, actual maps, raw maps and chosen target assignments remain fixed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

private theorem append_same_erased_context
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (E : proofEraseCtx Γ = proofEraseCtx Γ')
    (hAs : OnCtx (As ++ Γ) (env.IsType univs)) :
    OnCtx (As ++ Γ') (env.IsType univs) ∧
      proofEraseCtx (As ++ Γ) = proofEraseCtx (As ++ Γ') := by
  induction As with
  | nil => exact ⟨hΓ', E⟩
  | cons A As ih =>
    obtain ⟨hTail, u, hA⟩ := hAs
    obtain ⟨hTail', ET⟩ := ih hTail
    have C := proofEraseCtx_defeq hTail hTail' ET
    refine ⟨⟨hTail', u, hA.defeqDFC henv C⟩, ?_⟩
    change proofErase (As ++ Γ) A :: proofEraseCtx (As ++ Γ) =
      proofErase (As ++ Γ') A :: proofEraseCtx (As ++ Γ')
    have EA : proofErase (As ++ Γ) A = proofErase (As ++ Γ') A := proofErase_defeqCtx hTail C hA
    rw [EA, ET]

/-- Rebuild an unused insertion over another well-formed realization of the
same erased lower context. The upper raw context stays exactly the same.
This reconciles independently realized lower annotation certificates without
identifying their actual declarations syntactically. -/
theorem rebase_insertion_erased
    (W : Ctx.LiftN count offset Γ Λ)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΛ : OnCtx Λ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (E : proofEraseCtx Γ = proofEraseCtx Γ') :
    ∃ Λ', OnCtx Λ' (env.IsType univs) ∧ Ctx.LiftN count offset Γ' Λ' ∧
      proofEraseCtx Λ = proofEraseCtx Λ' := by
  induction W generalizing Γ' with
  | zero As hlen =>
    obtain ⟨hAs, EA⟩ := append_same_erased_context hΓ' E hΛ
    exact ⟨As ++ Γ', hAs, .zero As hlen, EA⟩
  | @succ offset Γ Λ A W ih =>
    cases Γ' with
    | nil => cases E
    | cons B Γ' =>
      obtain ⟨hΓ, u, hA⟩ := hΓ
      obtain ⟨hΛ, _, _⟩ := hΛ
      obtain ⟨hΓ', z, hB⟩ := hΓ'
      obtain ⟨EA, EΓ⟩ := List.cons.inj E
      obtain ⟨Λ', hΛ', W', EΛ⟩ := ih hΓ hΛ hΓ' EΓ
      refine ⟨B.liftN count offset :: Λ', ⟨hΛ', z, hB.weakN henv W'⟩, W'.succ, ?_⟩
      simp only [proofEraseCtx, proofErase_liftN hΓ hΛ W hA,
        proofErase_liftN hΓ' hΛ' W' hB, EA, EΛ]

/-- Source conversion preserves a paired frame with exactly the same actual
and erased maps and both original target assignments. Only the source context
is converted; the outgoing context remains fixed. -/
theorem EqSpecializationFrame.source_convert
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (C : IsDefEqCtx env univs [] Γ Γ₁) :
    EqSpecializationFrame Γ₁ Γ' Δ σ σ' ρ τ := by
  have HS := substEq_source_convert hΔ C W.agree.left
  have HC := EqSpecializationFrame.of_conversion hΔ HS (C.symm henv.ordered)
  have HH := HC.compose hΔ W
  have Eρ : VExpr.Subst.id.comp ρ = ρ := by funext i; rfl
  have Eτ : ProofShape.Subst.id.comp τ = τ := by funext i; rfl
  simpa only [Eρ, Eτ] using HH

/-- Descend an actual annotation computation through every recorded insertion.
Each source block is rebuilt with the same count and offset. All outgoing
contexts and maps are retained verbatim; no guarded path is substituted or
transported to an outgoing context. The lower annotation certificate is kept. -/
theorem EqFrameInsertionChain.compute_context
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (R : AnnotationContextCompute Step (proofEraseCtx Λ) Ξ) :
    ∃ Γ₁ Λ₁, IsDefEqCtx env univs [] Γ Γ₁ ∧ IsDefEqCtx env univs [] Λ Λ₁ ∧
      proofEraseCtx Λ₁ = Ξ ∧ AnnotationContextCompute Step (proofEraseCtx Γ) (proofEraseCtx Γ₁) ∧
      EqFrameInsertionChain Γ₁ Γ' ρ τ Λ₁ Λ' κ υ blocks := by
  induction J generalizing Ξ with
  | refl =>
    obtain ⟨Γ₁, _, C, E⟩ := R.realize hstep.descent W.actual.wf rfl
    exact ⟨Γ₁, Γ₁, C, C, E, E.symm ▸ R, .refl⟩
  | @step Λ Λ' κ υ blocks Ψ Ψ' n k χ ω J I ih =>
    have hΛ := (J.actual W).2.1.wf
    obtain ⟨Λ₁, Ψ₁, hΛ₁, hΨ₁, I₁, CΛ, CΨ, EΨ, RL⟩ :=
      R.descend_insertion hstep hΛ I.actual.wf I.source rfl
    obtain ⟨Γ₁, Λ₂, CΓ, CΛ₂, EΛ₂, RΓ, J₂⟩ := ih RL
    have hΛ₂ := (CΛ₂.symm henv.ordered).isType
    obtain ⟨Ψ₂, hΨ₂, I₂, EΨ₂⟩ := rebase_insertion_erased I₁ hΛ₁ hΨ₁ hΛ₂ EΛ₂.symm
    have CΨ₂ := CΨ.trans_empty henv (proofEraseCtx_defeq hΨ₁ hΨ₂ EΨ₂)
    have IN : EqFrameInsertion Λ₂ Λ' Ψ₂ Ψ' n k κ υ χ ω :=
      ⟨I₂, I.target, I.target_wf, substEq_source_convert I.target_wf CΨ₂ I.actual,
        (by intro i A hl hn; exact ErasedSubstAgreement.source_convert CΨ₂ I.erase hl hn),
        I.semantic, I.erased⟩
    exact ⟨Γ₁, Ψ₂, CΓ, CΨ₂, EΨ₂.symm.trans EΨ, RΓ, J₂.step IN⟩

/-- Every finite recorded annotation history preserves the full paired chain.
The lower source realizes the descended history, while all actual and erased
maps and outgoing contexts stay fixed. Each native annotation certificate is
used in its original source scope and at its own finite stage. -/
theorem EqFrameInsertionChain.context_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (R : PiInertContextHistory D Ξ Ξ')
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (E : proofEraseCtx Λ = Ξ) :
    ∃ Γ₁ Λ₁, IsDefEqCtx env univs [] Γ Γ₁ ∧ IsDefEqCtx env univs [] Λ Λ₁ ∧
      proofEraseCtx Λ₁ = Ξ' ∧ PiInertContextHistory D (proofEraseCtx Γ) (proofEraseCtx Γ₁) ∧
      EqFrameInsertionChain Γ₁ Γ' ρ τ Λ₁ Λ' κ υ blocks := by
  induction R generalizing Γ Λ with
  | refl =>
    exact ⟨Γ, Λ, .refl W.actual.wf, .refl (J.actual W).2.1.wf, E, .refl, J⟩
  | @step n Ξ Θ Ξ' RD RH ih =>
    obtain ⟨Γ₁, Λ₁, CΓ, CΛ, EΛ, RΓ, J₁⟩ :=
      J.compute_context (pi_inert_stage_certificate_descent heq hs n) W (E.symm ▸ RD)
    obtain ⟨Γ₂, Λ₂, CΓ₂, CΛ₂, EΛ₂, RΓ₂, J₂⟩ :=
      ih J₁ (W.source_convert hΔ CΓ) EΛ
    exact ⟨Γ₂, Λ₂, CΓ.trans_empty henv CΓ₂, CΛ.trans_empty henv CΛ₂,
      EΛ₂, .step RΓ RΓ₂, J₂⟩

/-- The chosen prefix, agreeing frame, exact erased argument vector and entire
insertion chain survive a finite actual annotation history. The actual prefix
and its assigned type do not change; source contexts are converted. In
particular no fresh existential target assignment replaces either chosen one. -/
theorem EqPrefixSpecializationAt.chain_context_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (R : PiInertContextHistory D (proofEraseCtx Λ) Ξ) :
    ∃ Γ₁ Λ₁, IsDefEqCtx env univs [] Γ Γ₁ ∧ IsDefEqCtx env univs [] Λ Λ₁ ∧
      proofEraseCtx Λ₁ = Ξ ∧
      EqPrefixSpecializationAt Γ₁ Δ v w v' w' original pre σ pending ∧
      EqSpecializationFrame Γ₁ Γ' Δ σ σ' ρ τ ∧
      EqFrameInsertionChain Γ₁ Γ' ρ τ Λ₁ Λ' κ υ blocks ∧
      env.HasType univs Γ₁ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F ∧
      pre.map (proofErase Γ₁) = pre.map (proofErase Γ) := by
  obtain ⟨Γ₁, Λ₁, CΓ, CΛ, EΛ, _, J₁⟩ := J.context_history heq hs hΔ R W rfl
  refine ⟨Γ₁, Λ₁, CΓ, CΛ, EΛ, H.source_convert hΔ CΓ,
    W.source_convert hΔ CΓ, J₁, hf.defeqDFC henv CΓ, ?_⟩
  apply List.map_congr_left
  intro e he
  obtain ⟨Te, ht⟩ := (mkApps_arguments_wf henv H.1.wf ⟨_, hf⟩).2 e he
  exact (proofErase_defeqCtx H.1.wf CΓ ht).symm

/-- Resume actual component computation in the changed upper source scope.
The full recorded annotation history is handled first, and the new component
certificates are then descended in their own actual context. Both chosen
target assignments survive, with exact agreement at the raw outgoing endpoint.
No component or native-guard path is transported through context conversion. -/
theorem EqPrefixSpecializationAt.chain_context_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (R : PiInertContextHistory D (proofEraseCtx Λ) Ξ)
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute Step Ξ)
      ((pre.map (proofErase Γ)).map blocks.erased) raw) :
    ∃ Γ₁ Λ₁ pre', proofEraseCtx Λ₁ = Ξ ∧
      EqSpecializationFrame Γ₁ Γ' Δ σ σ' ρ τ ∧
      EqFrameInsertionChain Γ₁ Γ' ρ τ Λ₁ Λ' κ υ blocks ∧
      EqPrefixSpecializationAt Γ₁ Δ v w v'' w'' original pre' σ pending ∧
      EqPrefixSpecializationAt Γ' Δ v w v'' w'' original (pre'.map (·.subst ρ)) σ' pending ∧
      env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.subst ρ))) (F.subst ρ) ∧
      ((pre'.map (proofErase Γ₁)).map blocks.erased) = raw ∧
      (((pre'.map (·.subst ρ)).map (proofErase Γ')).map blocks.erased) = raw.map (·.subst υ) ∧
      env.IsDefEq univs Γ₁ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F := by
  obtain ⟨Γ₁, Λ₁, CΓ, _, EΛ, H₁, W₁, J₁, hf₁, Epre⟩ :=
    H.chain_context_history heq hs hΔ W J hf R
  have HC₁ : env.IsDefEqU univs Γ₁ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']) :=
    HC.imp fun _ HE => HE.defeqDFC henv CΓ
  have HA₁ : List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ₁))
      ((pre.map (proofErase Γ₁)).map blocks.erased) raw := by
    simpa only [EΛ, Epre] using HA
  obtain ⟨pre', HP, Hout, hout, Eraw, Eout, HE⟩ :=
    H₁.compute_insertion_chain hstep hΔ W₁ J₁ hf₁ HC₁ HA₁
  exact ⟨Γ₁, Λ₁, pre', EΛ, W₁, J₁, HP, Hout, hout, Eraw, Eout, HE⟩

end Lean4Lean.VEnv.Strengthening
