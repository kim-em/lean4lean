import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSaturatedPaired

/-! # Paired actual maps across unused binder insertions

A lower agreeing frame and its upper actual map commute with the same unused
insertion on both sides. Entering a dependent binder increases the insertion
offset while lifting both maps. Target assignments remain in the lower scopes;
inserted declarations never require target inhabitants.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A concrete insertion on each side of a frame, together with the actual
upper typed substitution. Semantic and erased commutation are retained on all
terms, allowing a later dependent binder to enter below the inserted block.
The lower agreeing frame is supplied separately; upper contexts do not acquire
new target assignments. -/
structure EqFrameInsertion (Γ Γ' Λ Λ' : List VExpr) (count offset : Nat)
    (ρ : VExpr.Subst) (τ : ProofShape.Subst) (κ : VExpr.Subst) (υ : ProofShape.Subst) : Prop where
  source : Ctx.LiftN count offset Γ Λ
  target : Ctx.LiftN count offset Γ' Λ'
  target_wf : OnCtx Λ' (env.IsType univs)
  actual : Ctx.SubstEq env univs Λ' κ κ Λ
  erase : ErasedSubstAgreement Λ Λ' κ υ
  semantic : ∀ e : VExpr, (e.liftN count offset).subst κ = (e.subst ρ).liftN count offset
  erased : ∀ e : ProofShape, (e.liftN count offset).subst υ = (e.subst τ).liftN count offset

/-- No inserted block: the upper actual map is the original agreeing frame. -/
theorem EqSpecializationFrame.no_insertion
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ) :
    EqFrameInsertion Γ Γ' Γ Γ' 0 0 ρ τ ρ τ := by
  refine ⟨Ctx.LiftN.zero [], Ctx.LiftN.zero [], W.target.wf, W.actual, W.erase, ?_, ?_⟩
  · intro e; simp only [VExpr.liftN_zero]
  · intro e; simp only [ProofShape.liftN_zero]

/-- Insert one actual unused binder on both sides of an agreeing frame.
Its outgoing domain is computed by the actual lower substitution, so the
commuting equations are derived without a target image for the binder. -/
theorem EqSpecializationFrame.insert_domain
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hA : env.HasType univs Γ A (.sort u)) :
    EqFrameInsertion Γ Γ' (A :: Γ) (A.subst ρ :: Γ') 1 0 ρ τ ρ.lift τ.lift := by
  refine ⟨Ctx.LiftN.one, Ctx.LiftN.one,
    ⟨W.target.wf, u, hA.subst henv.orderedStrong W.actual W.target.wf⟩,
    W.actual.lift henv.ordered hA,
    ErasedSubstAgreement.lift W.target.wf W.actual hA W.erase, ?_, ?_⟩
  · intro e; exact VExpr.lift_subst_lift
  · intro e; exact ProofShape.lift_subst_lift e τ

/-- The actual upper map interprets its exact raw source and target scopes. -/
theorem EqFrameInsertion.interpretation
    (I : EqFrameInsertion Γ Γ' Λ Λ' count offset ρ τ κ υ) :
    ContextSubstitution (proofEraseCtx Λ) (proofEraseCtx Λ') υ := by
  intro Ψ hΨ EΨ
  exact ContextSubstitution.of_typed I.target_wf I.actual I.erase hΨ EΨ

/-- Enter a new dependent binder below an existing unused insertion. Both
actual maps lift; the old insertion moves one position deeper. Commutation
of the new displayed domains follows from the stored semantic square, and
commutation under binders follows by applying the old square to a lambda.
No equality of new domains or target inhabitant of an inserted type is assumed. -/
theorem EqFrameInsertion.under_binder
    (I : EqFrameInsertion Γ Γ' Λ Λ' count offset ρ τ κ υ)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hA : env.HasType univs Γ A (.sort u)) :
    EqFrameInsertion (A :: Γ) (A.subst ρ :: Γ')
      (A.liftN count offset :: Λ) ((A.subst ρ).liftN count offset :: Λ')
      count (offset+1) ρ.lift τ.lift κ.lift υ.lift := by
  have hAup : env.HasType univs Λ (A.liftN count offset) (.sort u) := hA.weakN henv I.source
  have hAout := hA.subst henv.orderedStrong W.actual W.target.wf
  have hAoutUp : env.HasType univs Λ' ((A.subst ρ).liftN count offset) (.sort u) :=
    hAout.weakN henv I.target
  refine ⟨I.source.succ, I.target.succ, ⟨I.target_wf, u, hAoutUp⟩, ?_, ?_, ?_, ?_⟩
  · simpa only [I.semantic A] using I.actual.lift henv.ordered hAup
  · intro i T hl hn
    simpa only [I.semantic A] using
      ErasedSubstAgreement.lift I.target_wf I.actual hAup I.erase hl hn
  · intro e
    have E := I.semantic (.lam (.sort .zero) e)
    simp only [VExpr.liftN, VExpr.subst] at E
    exact (VExpr.lam.inj E).2
  · intro e
    have E := I.erased (.lam (.sort .zero) e)
    simp only [ProofShape.liftN, ProofShape.subst] at E
    exact (ProofShape.lam.inj E).2

/-- Reify actual component computations beneath a paired insertion, keeping
both lower chosen assignments. Following the upper map at the computed raw
endpoint is exactly the inserted outgoing lower specialization. This theorem
uses the original component path only in its original scope. -/
theorem EqPrefixSpecializationAt.compute_paired_insertion
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (I : EqFrameInsertion Γ Γ' Λ Λ' count offset ρ τ κ υ)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ))
      ((pre.map (proofErase Γ)).map (·.liftN count offset)) raw) :
    ∃ pre', EqPrefixSpecializationAt Γ Δ v w v'' w'' original pre' σ pending ∧
      EqPrefixSpecializationAt Γ' Δ v w v'' w'' original (pre'.map (·.subst ρ)) σ' pending ∧
      env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.subst ρ))) (F.subst ρ) ∧
      ((pre'.map (proofErase Γ)).map (·.liftN count offset)) = raw ∧
      (((pre'.map (·.subst ρ)).map (proofErase Γ')).map (·.liftN count offset)) = raw.map (·.subst υ) ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F := by
  obtain ⟨pre', HP, EP, HE⟩ := H.compute hstep H.1.wf I.actual.wf I.source hΔ hf HC HA
  obtain ⟨Hout, hout, Eout⟩ := HP.frame hΔ W HE.hasType.2
  refine ⟨pre', HP, Hout, hout, EP, ?_, HE⟩
  rw [← EP, Eout]
  simp only [List.map_map, Function.comp_def, I.erased]

/-- Open an actual recovered eta binder beneath a paired unused insertion.
Recovery and its domain sort descend to the lower chosen prefix. Its next
pending target term extends the lower agreeing frame; the upper actual map
and exact raw scope extend using the commuting insertion square. This handles
an existing insertion block at arbitrary depth, not just an empty ambient scope.
Composition of separated insertion blocks and later consumption remains open. -/
theorem EqPrefixSpecializationAt.eta_paired_insertion
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ (y :: rest))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (I : EqFrameInsertion Γ Γ' Λ Λ' count offset ρ τ κ υ)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (RN : ScopedTypeRecovery Guard (proofEraseCtx Λ)
      ((proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)).liftN count offset)
      (.forallE rawA rawB))
    (SD : DomainSort (proofEraseCtx Λ) rawA u) :
    ∃ A B,
      env.HasType univs Γ A (.sort u) ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B) ∧
      proofEraseCtx (A.liftN count offset :: Λ) = rawA :: proofEraseCtx Λ ∧
      EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original
        (pre.map VExpr.lift ++ [VExpr.bvar 0]) (σ.cons y) rest ∧
      EqSpecializationFrame (A :: Γ) (A.subst ρ :: Γ') Δ
        (σ.cons y) (σ'.cons y) ρ.lift τ.lift ∧
      EqFrameInsertion (A :: Γ) (A.subst ρ :: Γ')
        (A.liftN count offset :: Λ) ((A.subst ρ).liftN count offset :: Λ')
        count (offset+1) ρ.lift τ.lift κ.lift υ.lift ∧
      env.HasType univs (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B ∧
      ¬ IsProof (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) ∧
      ((proofErase (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0]))).liftN count (offset+1)) =
        .app (((proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)).liftN count offset).liftN 1)
          (etaArgument u) := by
  obtain ⟨A, B, hfPi, EA, _⟩ := proofErase_scoped_recovered_pi_descend
    hguard H.1.wf I.actual.wf I.source hf RN
  obtain ⟨_, hPi⟩ := hfPi.isType henv H.1.wf
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  have hA := (EA ▸ SD).descend H.1.wf I.actual.wf I.source hA
  obtain ⟨Hfresh, Wfresh, _, _, _⟩ := H.eta_frame hΔ W ht hA hfPi
  have Ectx : proofEraseCtx (A.liftN count offset :: Λ) = rawA :: proofEraseCtx Λ := by
    rw [proofEraseCtx, proofErase_liftN H.1.wf I.actual.wf I.source hA, EA]
  have hfw : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift
      (.forallE A.lift (B.liftN 1 1)) := hfPi.weak henv
  have Ebody : VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0]) =
      .app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift (.bvar 0) := by
    simp only [VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil,
      VExpr.lift, VExpr.liftN_mkApps, VExpr.liftN]
  have hb : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B := by
    rw [Ebody]
    simpa only [VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
  have EB := proofErase_eta_body H.1.wf hA hfPi hn
  rw [← Ebody] at EB
  have hnb : ¬ IsProof (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) := by
    intro hp
    rw [proofErase_eq_proof.2 hp] at EB
    cases EB
  refine ⟨A, B, hA, hfPi, Ectx, Hfresh, Wfresh, I.under_binder W hA, hb, hnb, ?_⟩
  rw [EB, ProofShape.liftN, etaArgument_liftN,
    ← ProofShape.liftN_comm (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
      count 1 offset 0 (Nat.zero_le _)]

/-- A real non-level cut below a paired insertion strictly descends with the
same paired insertion construction retained beneath its new eta binder.
Positive singleton guards read the original equation. Native recovery is
lowered before choosing the next target image; the actual smaller raw minimum
is then identified with the inserted lower eta body. A pending target argument
is required. Separated insertion blocks and later consumption still need their
own closure argument. -/
theorem EqPrefixSpecializationAt.inserted_hole_cut_eq_or_smaller
    {C : ScopedHole Ξ (proofEraseCtx Λ)}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' [α,a,M,minor,b] pre σ (y :: rest))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (I : EqFrameInsertion Γ Γ' Λ Λ' count offset ρ τ κ υ)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : SpineBinderHole C) (HT : TypedSource Ξ source)
    (RP : ScopedComputeCount (PiInertStage D n) cp Ξ source
      (C.plug (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        ((pre.map (proofErase Γ)).map (·.liftN count offset)))))
    (HR : PiInertStage D n (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map (·.liftN count offset))) target)
    (HN : ¬ LevelPrimitive univs
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map (·.liftN count offset))) target)
    (RT : ScopedComputeCount (PiInertStage D n) ct Ξ (C.plug target) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Ξ K endpoint ck)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU))
    (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Ξ source tail →
      K tail k → cost ≤ j+k) :
    env.IsDefEq univs Δ a b α ∨ ∃ A B u,
      env.HasType univs Γ A (.sort u) ∧ ct+ck < cost ∧
      PiInertTypedContinuationMinimum D Ω out (proofEraseCtx (A.liftN count offset :: Λ))
        ((proofErase (A :: Γ)
          (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0]))).liftN count (offset+1)) (ct+ck) ∧
      EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' [α,a,M,minor,b]
        (pre.map VExpr.lift ++ [VExpr.bvar 0]) (σ.cons y) rest ∧
      EqSpecializationFrame (A :: Γ) (A.subst ρ :: Γ') Δ
        (σ.cons y) (σ'.cons y) ρ.lift τ.lift ∧
      EqFrameInsertion (A :: Γ) (A.subst ρ :: Γ')
        (A.liftN count offset :: Λ) ((A.subst ρ).liftN count offset :: Λ')
        count (offset+1) ρ.lift τ.lift κ.lift υ.lift ∧
      env.HasType univs (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B ∧
      ¬ IsProof (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) := by
  have Ee := proofErase_const_spine H.1.wf hf hn
  have HP : EqHeadCompletion Δ v w [α,a,M,minor,b] (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map (·.liftN count offset))) := by
    refine ⟨Γ, Λ, count, offset, v', w', pre, F, H.1.wf, I.actual.wf, I.source, rfl,
      hf, hn, H.forget, ?_⟩
    rw [Ee, ProofShape.liftN_mkApps, ProofShape.liftN]
  have HP := (EqTargetPrefixCompletion.of_completion (IteratedAmbientEqCompletion.base HP)).embedding
  rcases HP.hole_cut_eq_or_smaller heq hs hreg hoff hRec hΔ ht
      HC HT RP HR HN RT HK HE HO hcost hmin with
    Hlower | ⟨k, rawA, rawB, u, _, _, RN, SD, hsmall, HM, _⟩
  · exact .inl Hlower
  · obtain ⟨A, B, hA, _, Ectx, Hfresh, Wfresh, Ifresh, hb, hnb, EB⟩ :=
      H.eta_paired_insertion (erased_static_structure_eta_expansion_stage_descent heq hs k)
        hΔ W I ht hf hn
        (by simpa only [Ee, ProofShape.liftN_mkApps, ProofShape.liftN] using RN) SD
    refine .inr ⟨A, B, u, hA, hsmall, ?_, Hfresh, Wfresh, Ifresh, hb, hnb⟩
    simpa only [Ectx, EB, Ee, ProofShape.liftN_mkApps, ProofShape.liftN] using HM

end Lean4Lean.VEnv.Strengthening
