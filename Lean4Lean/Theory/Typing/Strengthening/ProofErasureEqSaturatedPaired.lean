import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqChosenCut

/-! # Paired ancestry beneath the saturated proof binder

The fresh proof major has no chosen target image. Keep the older assignment
and agreeing frame below its actual unused insertion instead. Component paths
of the tracked prefix descend through that insertion before the old frame is
applied. No target inhabitant or substituted primitive history is required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Any displayed Pi domain at a typed five-argument canonical Eq prefix is
a proposition, including a domain chosen by native recovery after conversion. -/
theorem eq_rec_five_pi_domain_prop
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) pre) (.forallE A B))
    (hlen : pre.length = 5) : env.HasType univs Γ A (.sort .zero) := by
  obtain ⟨α, a, M, minor, b, rfl⟩ : ∃ α a M minor b, pre = [α,a,M,minor,b] := by
    cases pre with | nil => simp at hlen | cons x xs =>
    cases xs with | nil => simp at hlen | cons y ys =>
    cases ys with | nil => simp at hlen | cons z zs =>
    cases zs with | nil => simp at hlen | cons q qs =>
    cases qs with | nil => simp at hlen | cons r rs =>
    cases rs with
    | nil => exact ⟨_, _, _, _, _, rfl⟩
    | cons s ss => simp at hlen
  obtain ⟨hv, hw, hα, ha, hM, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, hf⟩
  have hfCanon := eqRecBeforeMajor_typed heq hv hw hα ha hM hm hb
  obtain ⟨⟨_, HD⟩, _⟩ := (hfCanon.uniqU henv hΓ hf).forallE_inv henv hΓ
  exact (HasType.eqApp heq hw hα ha hb).defeqU_l henv hΓ HD.toU

/-- The actual map of an agreeing frame lifts beneath an unused domain without
extending either target assignment. This interprets the new raw scope, but
intentionally does not assert a target image for its fresh binder. -/
theorem EqSpecializationFrame.unused_domain_interpretation
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hA : env.HasType univs Γ A (.sort u)) :
    ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx (A.subst ρ :: Γ')) τ.lift := by
  have hA' := hA.subst henv.orderedStrong W.actual W.target.wf
  have hΓA' : OnCtx (A.subst ρ :: Γ') (env.IsType univs) := ⟨W.target.wf, u, hA'⟩
  intro Ψ hΨ EΨ
  exact ContextSubstitution.of_typed hΓA' (W.actual.lift henv.ordered hA)
    (ErasedSubstAgreement.lift W.target.wf W.actual hA W.erase) hΨ EΨ

/-- Compute the tracked components beneath an unused actual binder, lower
those components, and follow the original agreeing frame. Both old target
assignments remain unchanged. The two lifted erased endpoints agree exactly;
no image for the fresh binder, and no computation after substitution, is used. -/
theorem EqPrefixSpecializationAt.compute_under_unused_frame
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hA : env.HasType univs Γ A (.sort u))
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx (A :: Γ)))
      ((pre.map (proofErase Γ)).map (·.liftN 1)) raw) :
    ∃ pre', EqPrefixSpecializationAt Γ Δ v w v'' w'' original pre' σ pending ∧
      EqPrefixSpecializationAt Γ' Δ v w v'' w'' original (pre'.map (·.subst ρ)) σ' pending ∧
      env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.subst ρ))) (F.subst ρ) ∧
      ((pre'.map (proofErase Γ)).map (·.liftN 1)) = raw ∧
      (((pre'.map (·.subst ρ)).map (proofErase Γ')).map (·.liftN 1)) = raw.map (·.subst τ.lift) ∧
      ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx (A.subst ρ :: Γ')) τ.lift := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨H.1.wf, u, hA⟩
  obtain ⟨pre', HP, EP, HE⟩ := H.compute hstep H.1.wf hΓA Ctx.LiftN.one hΔ hf HC HA
  obtain ⟨Hout, hout, Eout⟩ := HP.frame hΔ W HE.hasType.2
  refine ⟨pre', HP, Hout, hout, EP, ?_, W.unused_domain_interpretation hA⟩
  rw [← EP, Eout]
  simp only [List.map_map, Function.comp_def, ProofShape.lift_subst_lift]

/-- Saturated eta yields an actual proof-binder minimum. The older chosen
substitution and frame stay below the unused binder; the lifted actual map
interprets the new scope without assigning that binder a target inhabitant.
This is a one-step minimum result. Iterating through arbitrary later inserted
scopes and continuation consumption remains a separate obligation. -/
theorem EqPrefixSpecializationAt.saturated_hole_cut_eq_or_smaller
    {C : ScopedHole Ξ (proofEraseCtx Γ)}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' [α,a,M,minor,b] pre σ [])
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : SpineBinderHole C) (HT : TypedSource Ξ source)
    (RP : ScopedComputeCount (PiInertStage D n) cp Ξ source
      (C.plug (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ)))))
    (HR : PiInertStage D n (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ))) target)
    (HN : ¬ LevelPrimitive univs
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ))) target)
    (RT : ScopedComputeCount (PiInertStage D n) ct Ξ (C.plug target) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Ξ K endpoint ck)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU))
    (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Ξ source tail →
      K tail k → cost ≤ j+k) :
    env.IsDefEq univs Δ a b α ∨ ∃ A B,
      env.HasType univs Γ A (.sort .zero) ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B) ∧
      target = .lam (proofErase Γ A)
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          ((pre.map (proofErase Γ)).map (·.liftN 1) ++ [.proof])) ∧
      ct+ck < cost ∧
      PiInertTypedContinuationMinimum D Ω out (proofEraseCtx (A :: Γ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          ((pre.map (proofErase Γ)).map (·.liftN 1) ++ [.proof])) (ct+ck) ∧
      EqPrefixSpecializationAt Γ' Δ v w v' w' [α,a,M,minor,b]
        (pre.map (·.subst ρ)) σ' [] ∧
      ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx (A.subst ρ :: Γ')) τ.lift ∧
      EqTargetPrefixEmbedding Δ v w [α,a,M,minor,b] (proofEraseCtx (A :: Γ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          ((pre.map (proofErase Γ)).map (·.liftN 1) ++ [.proof])) := by
  rcases (H.embedding hf hn).hole_cut_eq_or_smaller heq hs hreg hoff hRec hΔ ht
      HC HT RP HR HN RT HK HE HO hcost hmin with
    Hlower | ⟨k, rawA, rawB, u, Etarget, _, RN, SD, hsmall, HM, HPfresh⟩
  · exact .inl Hlower
  · have Ee := proofErase_const_spine H.1.wf hf hn
    obtain ⟨A, B, hfPi, EA, _⟩ := proofErase_scoped_recovered_pi_descend
      (erased_static_structure_eta_expansion_stage_descent heq hs k)
      H.1.wf H.1.wf (Ctx.LiftN.zero []) hf
      (by simpa only [List.length_nil, ProofShape.liftN_zero, Ee] using RN)
    have EA : proofErase Γ A = rawA := by
      simpa only [List.length_nil, ProofShape.liftN_zero] using EA
    have hlen : pre.length = 5 := by
      have HL := H.2.2.length_eq
      simpa only [List.length_cons, List.length_nil, List.length_append, List.length_map,
        Nat.add_zero, Nat.reduceAdd] using HL.symm
    have hA := eq_rec_five_pi_domain_prop heq H.1.wf hfPi hlen
    have SD' : DomainSort (proofEraseCtx Γ) ((proofErase Γ A).liftN 0) u := by
      simpa only [ProofShape.liftN_zero, EA] using SD
    have hAu := SD'.descend H.1.wf H.1.wf (Ctx.LiftN.zero []) hA
    have Earg : etaArgument u = .proof :=
      if_pos ((hAu.uniqU henv H.1.wf hA).sort_inv henv H.1.wf)
    have ES : .app ((ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ))).liftN 1)
        (etaArgument u) = ProofShape.mkApps (.const ``Eq.rec [v',w'])
          ((pre.map (proofErase Γ)).map (·.liftN 1) ++ [.proof]) := by
      simp only [Earg, ProofShape.liftN_mkApps, ProofShape.liftN, ProofShape.mkApps_append, ProofShape.mkApps]
    obtain ⟨Hout, _, _⟩ := H.frame hΔ W hf
    refine .inr ⟨A, B, hA, hfPi, ?_, hsmall, ?_, Hout, W.unused_domain_interpretation hA, ?_⟩
    · simpa only [EA, ES] using Etarget
    · simpa only [proofEraseCtx, EA, ES] using HM
    · simpa only [proofEraseCtx, EA, ES] using HPfresh

/-- A smaller saturated eta-body minimum retaining its old lower assignment
and agreeing frame. Its sixth argument is the literal proof marker; only the
five lower arguments are specialized. The scope interpretation is the lifted
actual frame, not a claimed target assignment for the proof binder. -/
def UnusedPairedEqBodyMinimum (D : Definitions) (Γ Γ' Δ : List VExpr) (v w : VLevel)
    (original : List VExpr) (σ σ' ρ : VExpr.Subst) (τ : ProofShape.Subst)
    (Ω : List ProofShape) (out : ProofShape) (budget : Nat) : Prop :=
  ∃ A B v' w' pre smaller,
    env.HasType univs Γ A (.sort .zero) ∧ pre.length = 5 ∧ smaller < budget ∧
    env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B) ∧
    ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) ∧
    EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ [] ∧
    EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ ∧
    EqPrefixSpecializationAt Γ' Δ v w v' w' original (pre.map (·.subst ρ)) σ' [] ∧
    ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx (A.subst ρ :: Γ')) τ.lift ∧
    PiInertTypedContinuationMinimum D Ω out (proofEraseCtx (A :: Γ))
      (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        ((pre.map (proofErase Γ)).map (·.liftN 1) ++ [.proof])) smaller ∧
    EqTargetPrefixEmbedding Δ v w original (proofEraseCtx (A :: Γ))
      (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        ((pre.map (proofErase Γ)).map (·.liftN 1) ++ [.proof]))

/-- Every chosen actual cut reads the equation or strictly descends with its
older frame retained. A short prefix extends both target assignments; a full
prefix inserts a proof binder above their old scopes. The former terminal
five-slot cut alternative is thereby replaced by an actual smaller minimum.
Closure of the unused-binder representation under the full subsequent descent
and arbitrary continuation consumption is not asserted here. -/
theorem ChosenEqSpineCut.eq_or_paired_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : ChosenEqSpineCut D Γ Δ v w [α,a,M,minor,b] σ pending n source endpoint budget)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (HT : TypedSource (proofEraseCtx Γ) source)
    (HK : PiInertTypedContinuationRun D Ω out (proofEraseCtx Γ) K endpoint ck)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU))
    (hcost : budget+ck ≤ cost)
    (hmin : ∀ later j tail k,
      ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ) source tail →
        K tail k → cost ≤ j+k) :
    env.IsDefEq univs Δ a b α ∨
    PairedEqBodyMinimum D Γ Γ' Δ v w [α,a,M,minor,b] σ σ' ρ τ Ω out cost ∨
    UnusedPairedEqBodyMinimum D Γ Γ' Δ v w [α,a,M,minor,b] σ σ' ρ τ Ω out cost := by
  rcases H.eq_or_paired_smaller_or_saturated heq hs hreg hoff hRec hΔ ht W HT HK HE HO hcost hmin with
    Hlower | Hpaired | ⟨v', w', pre, F, target, cp, ct, hlen, HP, hf, hn, hc, RP, HR, HN, RT⟩
  · exact .inl Hlower
  · exact .inr (.inl Hpaired)
  · rcases HP.saturated_hole_cut_eq_or_smaller (C := .hole) heq hs hreg hoff hRec hΔ ht W hf hn
        .hole HT RP HR HN RT HK HE HO (cost := cost) (by omega) hmin with
      Hlower | ⟨A, B, hA, hfPi, _, hsmall, HM, Hout, WI, Hembed⟩
    · exact .inl Hlower
    · exact .inr (.inr ⟨A, B, v', w', pre, ct+ck, hA, hlen, hsmall, hfPi, hn,
        HP, W, Hout, WI, HM, Hembed⟩)

end Lean4Lean.VEnv.Strengthening
