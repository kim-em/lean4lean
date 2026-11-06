import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSupplyInsertionSquare

/-! # Supplied histories with interleaved unused retained binders

A chosen binder extends the lower assignment and shifts both insertion paths.
An unused binder appends an actual upper insertion and preserves that assignment.
Both retain their computed annotation and actual lambda wrapper. Separate counts
record lower chosen binders and all retained frames.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Finite actual retained histories with chosen and unused binders interleaved.
Unused domains can depend on the whole current upper context; they need no
chosen image. Annotation computations stay in their original source scopes. -/
inductive EqInterleavedSupplyHistory (D : Definitions) (Δ Γ₀ Λ₀ : List VExpr)
    (σ₀ : VExpr.Subst) (blocks₀ : EqInsertionPath) (Ψ₀ : List ProofShape)
    (υ₀ : ProofShape.Subst) :
    List VExpr → List VExpr → VExpr.Subst → EqInsertionPath →
    List ProofShape → ProofShape.Subst → (ProofShape → ProofShape) → Nat → Nat → Prop where
  | base : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
      Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀ id 0 0
  | retained : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
        Γ Λ σ blocks Ψ υ plug chosen depth →
      env.HasType univs Γ A (.sort u) → env.HasType univs Δ y (A.subst σ) →
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ)
        (blocks.erased (proofErase Γ A)) rawA' →
      EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
        (A :: Γ) (blocks.actual A :: Λ) (σ.cons y) blocks.underBinder
        (rawA'.subst υ :: Ψ) υ.lift
        (fun e => plug (ProofShape.mkApps (.lam rawA' e) args)) (chosen+1) (depth+1)
  | unused : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
        Γ Λ σ blocks Ψ υ plug chosen depth →
      env.HasType univs Λ A (.sort u) →
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ) (proofErase Λ A) rawA' →
      EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
        Γ (A :: Λ) σ (blocks ++ [(1,0)]) (rawA'.subst υ :: Ψ) υ.lift
        (fun e => plug (ProofShape.mkApps (.lam rawA' e) args)) chosen (depth+1)

/-- The earlier chosen-only telescope is the case where every actual binder
has a chosen image. Its wrappers and native annotation paths are preserved. -/
theorem EqRetainedSupplyHistory.interleaved
    (H : EqRetainedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀ Γ Λ σ blocks Ψ υ plug depth) :
    EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
      Γ Λ σ blocks Ψ υ plug depth depth := by
  induction H with
  | base => exact .base
  | binder _ hA hy RD ih => exact .retained ih hA hy RD

/-- Outgoing contexts and the raw map can be filled in after the source
history is recorded. All source annotations, native paths, chosen images,
insertions and wrappers remain unchanged. This does not assert agreement with
an arbitrary consumed argument: the later realization must derive that base
agreement from the actual supplied-argument computation. -/
theorem EqInterleavedSupplyHistory.rebase_endpoint
    (H : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
      Γ Λ σ blocks Ψ υ plug chosen depth)
    (newTarget : List ProofShape) (newMap : ProofShape.Subst) :
    ∃ Ψ' υ', EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ newTarget newMap
      Γ Λ σ blocks Ψ' υ' plug chosen depth := by
  induction H with
  | base => exact ⟨_, _, .base⟩
  | retained _ hA hy RD ih =>
    obtain ⟨Ψ', υ', HR⟩ := ih
    exact ⟨_, _, .retained HR hA hy RD⟩
  | unused _ hA RD ih =>
    obtain ⟨Ψ', υ', HR⟩ := ih
    exact ⟨_, _, .unused HR hA RD⟩

/-- The recorded wrappers are an actual counted retained prefix. Both chosen
and unused cases derive their native domain-sort and context interpretation
from the source insertion chain, without giving unused domains target images. -/
theorem EqInterleavedSupplyHistory.retained_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
      Γ Λ σ blocks Ψ υ plug chosen depth)
    (S : Ctx.SubstEq env univs Δ σ₀ σ₀ Γ₀)
    (J : EqFrameInsertionChain Γ₀ Γ₀ VExpr.Subst.id ProofShape.Subst.id
      Λ₀ Λ₀ VExpr.Subst.id ProofShape.Subst.id blocks₀) :
    Ctx.SubstEq env univs Δ σ σ Γ ∧
      EqFrameInsertionChain Γ Γ VExpr.Subst.id ProofShape.Subst.id
        Λ Λ VExpr.Subst.id ProofShape.Subst.id blocks ∧
      PiInertRetainedPrefixCount D (proofEraseCtx Λ) (proofEraseCtx Λ₀) plug depth := by
  induction H with
  | base => exact ⟨S, J, .refl⟩
  | @retained Γ Λ σ blocks Ψ υ plug chosen depth A u y n cd rawA' args H hA hy RD ih =>
    obtain ⟨S, J, HP⟩ := ih
    have W := EqSpecializationFrame.of_conversion hΔ S (.refl S.wf)
    have hΛ := (J.actual W).2.1.wf
    have hAup : env.HasType univs Λ (blocks.actual A) (.sort u) := by
      simpa only [EqInsertionPath.actual_sort] using J.weak hA
    have SD : DomainSort (proofEraseCtx Λ) (blocks.erased (proofErase Γ A)) u :=
      ⟨Λ, blocks.actual A, hΛ, rfl, hAup, J.erase_actual W hA⟩
    refine ⟨.cons S hA hy, ?_, ?_⟩
    · simpa only [VExpr.id_lift, ProofShape.Subst.id_lift, VExpr.subst_id] using J.under_binder W hA
    · simpa only [proofEraseCtx, J.erase_actual W hA] using
        PiInertRetainedPrefixCount.retained SD RD (pi_inert_retained_frame_interpretation heq hs SD RD) HP
  | @unused Γ Λ σ blocks Ψ υ plug chosen depth A u n cd rawA' args H hA RD ih =>
    obtain ⟨S, J, HP⟩ := ih
    have W := EqSpecializationFrame.of_conversion hΔ S (.refl S.wf)
    have SD : DomainSort (proofEraseCtx Λ) (proofErase Λ A) u :=
      ⟨Λ, A, (J.actual W).2.1.wf, rfl, hA, rfl⟩
    refine ⟨S, ?_, ?_⟩
    · simpa only [VExpr.id_lift, ProofShape.Subst.id_lift, VExpr.subst_id] using J.insert_domain W hA
    · exact PiInertRetainedPrefixCount.retained SD RD
        (pi_inert_retained_frame_interpretation heq hs SD RD) HP

/-- Every actual binder lifts the raw map, but only chosen binders extend the
lower assignment. The counts therefore remain separate even at equal cost. -/
theorem EqInterleavedSupplyHistory.shape
    (H : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
      Γ Λ σ blocks Ψ υ plug chosen depth) :
    chosen ≤ depth ∧ υ = υ₀.liftN depth := by
  induction H with
  | base => exact ⟨Nat.le_refl _, rfl⟩
  | retained _ _ _ _ ih =>
    obtain ⟨h, rfl⟩ := ih
    exact ⟨by omega, rfl⟩
  | unused _ _ _ ih =>
    obtain ⟨h, rfl⟩ := ih
    exact ⟨by omega, rfl⟩

/-- Realize the complete interleaved history. The lower agreeing map lifts
only at chosen binders; the upper typed map lifts at every actual retained
binder. Each outgoing insertion and computed annotation is constructed in order,
so inserted domains may depend on previously retained chosen or unused binders. -/
theorem EqInterleavedSupplyHistory.realize
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ incoming Ψ₀ υ₀
      Γ Λ σ blocks Ψ υ plug chosen depth)
    (Q : EqSupplyInsertionSquare Γ₀ Γ₀' Δ σ₀ σ₀' ρ₀ τ₀ Λ₀ Λ₀' κ₀ υ₀ incoming outgoing)
    (EΨ : Ψ₀ = proofEraseCtx Λ₀') :
    ∃ (Γ' Λ' : List VExpr) (σ' : VExpr.Subst) (outblocks : EqInsertionPath),
      EqSupplyInsertionSquare Γ Γ' Δ σ σ' (ρ₀.liftN chosen) (τ₀.liftN chosen)
        Λ Λ' (κ₀.liftN depth) υ blocks outblocks ∧ Ψ = proofEraseCtx Λ' := by
  induction H with
  | base => exact ⟨Γ₀', Λ₀', σ₀', outgoing, Q, EΨ⟩
  | @retained Γ Λ σ blocks Ψ υ plug chosen depth A u y n cd rawA' args H hA hy RD ih =>
    obtain ⟨Γ', Λ', σ', outblocks, Q, EΨ⟩ := ih
    obtain ⟨B, _, _, Qnew, EB⟩ := Q.retained heq hs hΔ hA hy RD.forget
    exact ⟨_, _, _, _, Qnew, by simp only [proofEraseCtx, ← EΨ, EB]⟩
  | @unused Γ Λ σ blocks Ψ υ plug chosen depth A u n cd rawA' args H hA RD ih =>
    obtain ⟨Γ', Λ', σ', outblocks, Q, EΨ⟩ := ih
    obtain ⟨B, _, _, Qnew, EB⟩ := Q.unused heq hs hΔ hA RD.forget
    exact ⟨_, _, _, _, Qnew, by simp only [proofEraseCtx, ← EΨ, EB]⟩

/-- Read the actual whole retained suffix at the precise interleaved body
context. The lambda readouts preserve unrestricted competitors and add one
frame for every actual retained binder, including unused inserted binders. -/
theorem EqInterleavedSupplyHistory.focus_nonempty
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
      Γ Λ σ blocks Ψ υ plug chosen depth)
    (hd : 0 < depth)
    (HM : PiInertFrameMinimum D Ω out Ψ₀
      (ProofShape.mkApps ((plug e).subst υ₀) pending) cost frames) :
    ∃ smaller, smaller ≤ cost ∧
      PiInertFrameMinimum D Ω out Ψ (e.subst υ) smaller (frames+depth) := by
  induction H generalizing e pending cost frames with
  | base => omega
  | @retained Γ Λ σ blocks Ψ υ plug chosen depth A u y n cd rawA' args H hA hy RD ih =>
    by_cases hz : depth = 0
    · subst depth
      cases H with
      | base =>
        simp only [id_eq, ProofShape.subst_mkApps, ProofShape.subst, ← ProofShape.mkApps_append] at HM
        obtain ⟨smaller, hsmall, HMbody⟩ := HM.lambda_body heq hs
        exact ⟨smaller, hsmall, HMbody⟩
    · obtain ⟨smaller, hsmall, HMinner⟩ := ih (by omega) HM
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at HMinner
      obtain ⟨last, hlast, HMbody⟩ := HMinner.lambda_body heq hs
      exact ⟨last, Nat.le_trans hlast hsmall, by simpa only [Nat.add_assoc] using HMbody⟩
  | @unused Γ Λ σ blocks Ψ υ plug chosen depth A u n cd rawA' args H hA RD ih =>
    by_cases hz : depth = 0
    · subst depth
      cases H with
      | base =>
        simp only [id_eq, ProofShape.subst_mkApps, ProofShape.subst, ← ProofShape.mkApps_append] at HM
        obtain ⟨smaller, hsmall, HMbody⟩ := HM.lambda_body heq hs
        exact ⟨smaller, hsmall, HMbody⟩
    · obtain ⟨smaller, hsmall, HMinner⟩ := ih (by omega) HM
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at HMinner
      obtain ⟨last, hlast, HMbody⟩ := HMinner.lambda_body heq hs
      exact ⟨last, Nat.le_trans hlast hsmall, by simpa only [Nat.add_assoc] using HMbody⟩

/-- Actual supplied-argument computation provides the base for arbitrary
interleavings. Its chosen image is the original argument specialization;
inserted domains introduce no additional chosen-image agreement premise. -/
theorem EqInterleavedSupplyHistory.consume
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (harg : ErasedScopedPrimitiveCertificateDescent ArgStep ArgStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω incoming)
    (hA : env.HasType univs Γ₀ A (.sort u)) (hx : env.HasType univs Γ₀ x A)
    (RX : ScopedCompute ArgStep (proofEraseCtx Λ₀) (incoming.erased (proofErase Γ₀ x)) rawX)
    (H : EqInterleavedSupplyHistory D Δ (A :: Γ₀) (incoming.actual A :: Λ₀)
      (σ₀.cons (x.subst σ₀)) incoming.underBinder (proofEraseCtx Λ₀)
      (ProofShape.Subst.one rawX) Γ Λ σ blocks Ψ υ plug chosen depth) :
    ∃ (x' : VExpr) (Γ' Λ' : List VExpr) (σ' : VExpr.Subst) (outblocks : EqInsertionPath),
      env.IsDefEq univs Γ₀ x x' A ∧ incoming.erased (proofErase Γ₀ x') = rawX ∧
      EqSupplyInsertionSquare Γ Γ' Δ σ σ' ((VExpr.Subst.one x').liftN chosen)
        ((ProofShape.Subst.one (proofErase Γ₀ x')).liftN chosen)
        Λ Λ' ((VExpr.Subst.one (incoming.actual x')).liftN depth) υ blocks outblocks ∧
      Ψ = proofEraseCtx Λ' := by
  obtain ⟨x', HX, EX, Q⟩ := EqSupplyInsertionSquare.supplied harg hΔ W J hA hx RX
  obtain ⟨Γ', Λ', σ', outblocks, Qnew, EΨ⟩ := H.realize heq hs hΔ Q rfl
  exact ⟨x', Γ', Λ', σ', outblocks, HX, EX, Qnew, EΨ⟩

open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

/-- Lower actual components through the incoming path, then execute the
agreeing square and return to the chosen-chain minimum class through its
separate outgoing path. The exact raw endpoint, pending vector and type survive;
the given actual suffix minimum keeps its cost and all competitors. -/
theorem EqSupplyInsertionSquare.component_return
    (hbody : ErasedScopedPrimitiveCertificateDescent BodyStep BodyStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (Q : EqSupplyInsertionSquare Γ Γ' Δ σ σ' ρ τ Λ Λ' κ υ incoming outgoing)
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx Λ))
      ((pre.map (proofErase Γ)).map incoming.erased) rawBody)
    (hextra : extra = [] ∨ pending = [])
    (HM : PiInertTypedContinuationMinimum D Ω out (proofEraseCtx Λ')
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (rawBody.map (·.subst υ) ++ extra)) cost) :
    ∃ final, EqPrefixSpecializationAt Γ' Δ v w v'' w'' original final σ' pending ∧
      env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) final) (F.subst ρ) ∧
      ¬ IsProof Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) final) ∧
      ((final.map (proofErase Γ')).map outgoing.erased) = rawBody.map (·.subst υ) ∧
      EqChainContinuationMinimum D Δ v w original Ω out cost := by
  have WS := EqSpecializationFrame.of_conversion hΔ Q.lower.agree.left (.refl Q.lower.actual.wf)
  obtain ⟨pre', HP, _, _, Ebody, _, HE⟩ := H.compute_insertion_chain hbody hΔ WS Q.source hf HC HA
  obtain ⟨Hout, hout, Eout⟩ := HP.frame hΔ Q.lower HE.hasType.2
  have hnout : ¬ IsProof Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.subst ρ))) := by
    intro hp
    apply hn ((isProof_congr H.1.wf HE).2 ?_)
    apply (isProof_subst Q.lower.target.wf Q.lower.actual HE.hasType.2).1
    simpa only [VExpr.subst_mkApps, VExpr.subst] using hp
  have Efinal : (((pre'.map (·.subst ρ)).map (proofErase Γ')).map outgoing.erased) = rawBody.map (·.subst υ) := by
    rw [Eout, ← Ebody]
    simp only [List.map_map, Function.comp_def, Q.erased]
  refine ⟨_, Hout, hout, hnout, Efinal, ?_⟩
  have WT := EqSpecializationFrame.of_conversion hΔ Q.lower.target (.refl Q.lower.target.wf)
  refine ⟨Γ', Γ', Λ', Λ', σ', σ', VExpr.Subst.id, ProofShape.Subst.id,
    VExpr.Subst.id, ProofShape.Subst.id, outgoing, v'', w'', _, pending, extra, _,
    Hout, WT, Q.target, hout, hnout, hextra, ?_⟩
  simpa only [Efinal] using HM


/-- Execute an actual selected supplied consumption beneath interleaved chosen
and unused retained binders. The original body path and application predicate
derive the whole suffix minimum; wrapper readout derives the inner one, and
realization returns its components to the chosen-chain class. The history can
be recorded before the final consumed argument: its outgoing contexts and map
are filled in here from that actual argument. Untracked upper extras keep their
exact substituted syntax when the chosen prefix is complete. If primitive cost
is equal, the older application frame disappears relative to the recorded
retained prefix. The global gap is deriving and preserving this history at
arbitrary nested cuts, not an extra agreement or minimum premise here. -/
theorem EqPrefixSpecializationAt.interleaved_supply_selected_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hbody : ErasedScopedPrimitiveCertificateDescent BodyStep BodyStep)
    (harg : ErasedScopedPrimitiveCertificateDescent ArgStep ArgStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω incoming)
    (hA : env.HasType univs Γ₀ A (.sort u)) (hx : env.HasType univs Γ₀ x A)
    (RX : ScopedCompute ArgStep (proofEraseCtx Λ₀) (incoming.erased (proofErase Γ₀ x)) rawX)
    (HH : EqInterleavedSupplyHistory D Δ (A :: Γ₀) (incoming.actual A :: Λ₀)
      (σ₀.cons (x.subst σ₀)) incoming.underBinder historyTarget
      historyMap Γ Λ σ blocks Ψ υ plug chosen depth)
    (hd : 0 < depth)
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx Λ))
      ((pre.map (proofErase Γ)).map blocks.erased) rawBody)
    (hextra : rawExtra = [] ∨ pending = [])
    (RP : ScopedComputeCount (PiInertStage D n) cb (proofEraseCtx Λ) source
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (rawBody ++ rawExtra)))
    (HTnext : TypedSource (proofEraseCtx Λ₀)
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (rawBody ++ rawExtra))).subst
        (ProofShape.Subst.one rawX)) outerArgs))
    (RT : ScopedComputeCount (PiInertStage D m) cs (proofEraseCtx Λ₀)
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (rawBody ++ rawExtra))).subst
        (ProofShape.Subst.one rawX)) outerArgs) endpoint)
    (HK : PiInertRunFrames D Ω out (proofEraseCtx Λ₀) K endpoint ck frames)
    (hc : cb+(cs+ck) = cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Λ) source tail →
      PiInertApplicationContinuation D (proofEraseCtx Λ₀) (ProofShape.Subst.one rawX) outerArgs K
        (plug tail) k → cost ≤ j+k) :
    ∃ Ξ smaller, smaller ≤ cs+ck ∧
      PiInertFrameMinimum D Ω out Ξ
        (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
          (rawBody.map (·.subst ((ProofShape.Subst.one rawX).liftN depth)) ++
            rawExtra.map (·.subst ((ProofShape.Subst.one rawX).liftN depth))))
        smaller (frames+depth) ∧
      EqChainContinuationMinimum D Δ v w original Ω out smaller ∧
      (smaller < cost ∨ smaller = cost ∧ frames+depth < frames+depth+1) := by
  obtain ⟨Ξ, χ, HR⟩ := HH.rebase_endpoint (proofEraseCtx Λ₀) (ProofShape.Subst.one rawX)
  have HMnext : PiInertFrameMinimum D Ω out (proofEraseCtx Λ₀)
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (rawBody ++ rawExtra))).subst
        (ProofShape.Subst.one rawX)) outerArgs) (cs+ck) frames := by
    refine ⟨K, m, cs, ck, endpoint, HTnext, RT, HK, rfl, ?_⟩
    intro later j tail k RJ HL
    have HB := HM n cb _ (j+k) RP ⟨later, j, tail, k, rfl, RJ, HL⟩
    omega
  obtain ⟨smaller, hsmall, HB⟩ := HR.focus_nonempty heq hs hd HMnext
  have HB : PiInertFrameMinimum D Ω out Ξ
      (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
        (rawBody.map (·.subst χ) ++ rawExtra.map (·.subst χ)))
      smaller (frames+depth) := by
    simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_append] using HB
  obtain ⟨x', Γ', Λ', σ', outblocks, HX, EX, Q, EΨ⟩ := HR.consume heq hs harg hΔ W J hA hx RX
  have hextra' : rawExtra.map (·.subst χ) = [] ∨ pending = [] := by
    rcases hextra with rfl | hp
    · exact .inl rfl
    · exact .inr hp
  obtain ⟨final, HP, ht, hnout, Efinal, Hchain⟩ := Q.component_return hbody hΔ H hf hn HC HA
    (extra := rawExtra.map (·.subst χ)) hextra' (by simpa only [← EΨ] using HB.forget)
  exact ⟨Ξ, smaller, hsmall, by simpa only [HR.shape.2] using HB, Hchain, by omega⟩

end Lean4Lean.VEnv.Strengthening
