import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSpecializationFrames
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedContext

/-! # Recover the actual argument of a consumed endpoint binder

Normalize the interpreted older-variable map using its erased identity.
The consumed argument then has the original displayed type, and agreement
with its chosen target image is one concrete equality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A typed self-substitution with identity erasure acts as semantic identity
on every typed term. Type equality is first recovered from nonproof sort
assignments, so proof-valued terms are compared at their proper types. -/
theorem erased_identity_subst_eq
    (hΓ : OnCtx Γ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ ρ ρ Γ)
    (E : ErasedSubstAgreement Γ Γ ρ ProofShape.Subst.id)
    (he : env.HasType univs Γ e T) : env.IsDefEq univs Γ e (e.subst ρ) T := by
  obtain ⟨u, hT⟩ := he.isType henv hΓ
  have hTρ := hT.subst henv.orderedStrong W hΓ
  have ET : proofErase Γ T = proofErase Γ (T.subst ρ) := by
    simpa only [ProofShape.subst_id] using (proofErase_subst_with hΓ W hT E).symm
  obtain ⟨_, HT⟩ := (proofErase_reflect hΓ hT hTρ ET).2 (not_isProof_of_sort hΓ hT)
  have Ee : proofErase Γ e = proofErase Γ (e.subst ρ) := by
    simpa only [ProofShape.subst_id] using (proofErase_subst_with hΓ W he E).symm
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ he (he.subst henv.orderedStrong W hΓ) Ee).1 (HT.defeq hΓ)
  exact (HE.defeq hΓ).of_l henv hΓ he

/-- An interpreted one-binder endpoint map has an actual argument at the
original displayed domain. Older variables normalize to identity. Exact raw
agreement is required only when the consumed variable is not proof-valued;
no arbitrary proof marker is assigned an original representative. -/
theorem ProofShape.ContextSubstitution.realize_one
    (W : ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx Γ) (ProofShape.Subst.one rawX))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs)) :
    ∃ x, env.HasType univs Γ x A ∧
      (¬ IsProof (A :: Γ) (.bvar 0) → proofErase Γ x = rawX) ∧
      ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one x) (ProofShape.Subst.one rawX) := by
  obtain ⟨Γ₀, ρ, hΓ₀, EΓ₀, WR, ER⟩ := W hΓA rfl
  have C := proofEraseCtx_defeq hΓ₀ hΓA.1 EΓ₀
  have WR' : Ctx.SubstEq env univs Γ ρ ρ (A :: Γ) := by
    apply substEq_of_lookup hΓA
    intro i B hl
    exact (WR.lookup hl).hasType.1.defeqDFC henv C
  have ER' : ErasedSubstAgreement (A :: Γ) Γ ρ (ProofShape.Subst.one rawX) := by
    intro i B hl hn
    exact (proofErase_defeqCtx hΓ₀ C (WR.lookup hl).hasType.1).symm.trans (ER hl hn)
  have ERtail : ErasedSubstAgreement Γ Γ ρ.tail ProofShape.Subst.id := by
    intro i B hl hn
    exact (ER'.tail hΓA) hl hn
  cases WR' with
  | cons WT hA hx =>
    have HA := erased_identity_subst_eq hΓA.1 WT ERtail hA
    have hActual : env.HasType univs Γ ρ.head A := HA.symm.defeq hx
    refine ⟨ρ.head, hActual, (fun hn => ER' Lookup.zero hn), ?_⟩
    intro i B hl hn
    cases hl with
    | zero => exact ER' Lookup.zero hn
    | succ hl =>
      have hn' : ¬ IsProof Γ (.bvar _) := fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
      simp only [VExpr.Subst.one, VExpr.Subst.cons, VExpr.Subst.id,
        ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.Subst.id, proofErase, if_neg hn']

/-- After normalizing the actual map to one argument, target agreement is
exactly the equality for that consumed argument. The older target assignment
is the incoming assignment's tail; no additional older-variable equality is
required. Raw agreement still ignores proof-valued source variables. -/
theorem EqSpecializationFrame.inst_iff
    (W : Ctx.SubstEq env univs Δ σ.tail σ.tail Γ)
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x A)
    (ER : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one x) (ProofShape.Subst.one rawX)) :
    EqSpecializationFrame (A :: Γ) Γ Δ σ σ.tail (VExpr.Subst.one x) (ProofShape.Subst.one rawX) ↔
      env.IsDefEq univs Δ σ.head (x.subst σ.tail) (A.subst σ.tail) := by
  constructor
  · intro H
    cases H.agree with
    | cons _ _ Hhead => exact Hhead
  · intro Hxy
    have H := EqSpecializationFrame.inst W hA hx Hxy
    have Eσ : σ.tail.cons σ.head = σ := by funext i; cases i <;> rfl
    exact ⟨H.target, H.actual, ER, by simpa only [Eσ] using H.agree⟩

/-- An actual proof-valued binder needs no supplied target-image equality.
Its interpreted raw argument is realized at the original proposition; after
specialization, proof irrelevance agrees with the already chosen image. -/
theorem ProofShape.ContextSubstitution.proof_supply_frame
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx Γ) (ProofShape.Subst.one rawX))
    (HS : Ctx.SubstEq env univs Δ σ σ (A :: Γ))
    (hA : env.HasType univs Γ A (.sort .zero)) :
    ∃ x, env.HasType univs Γ x A ∧
      (¬ IsProof (A :: Γ) (.bvar 0) → proofErase Γ x = rawX) ∧
      EqSpecializationFrame (A :: Γ) Γ Δ σ σ.tail
        (VExpr.Subst.one x) (ProofShape.Subst.one rawX) := by
  obtain ⟨x, hx, EX, ER⟩ := W.realize_one HS.wf
  cases HS with
  | cons WT _ hy =>
    refine ⟨x, hx, EX, (EqSpecializationFrame.inst_iff WT hA hx ER).2 ?_⟩
    exact .proofIrrel (hA.subst henv.orderedStrong WT hΔ) hy
      (hx.subst henv.orderedStrong WT hΔ)

/-- Consuming a proof-valued source binder preserves its chosen Eq target
specialization and exact raw argument vector. The outgoing assignment is the
original tail, and the proof image's compatibility is derived automatically.
Ambient insertions outside this chosen semantic realization still require
separate ancestry handling. -/
theorem EqPrefixSpecializationAt.consume_proof_endpoint
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original pre σ pending)
    (W : ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx Γ) (ProofShape.Subst.one rawX))
    (hA : env.HasType univs Γ A (.sort .zero))
    (hf : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F) :
    ∃ x, env.HasType univs Γ x A ∧
      EqSpecializationFrame (A :: Γ) Γ Δ σ σ.tail
        (VExpr.Subst.one x) (ProofShape.Subst.one rawX) ∧
      EqPrefixSpecializationAt Γ Δ v w v' w' original (pre.map (·.inst x)) σ.tail pending ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map (·.inst x))) (F.inst x) ∧
      (pre.map (·.inst x)).map (proofErase Γ) = (pre.map (proofErase (A :: Γ))).map (·.inst rawX) := by
  obtain ⟨x, hx, _, HW⟩ := W.proof_supply_frame hΔ H.1 hA
  obtain ⟨HP, ht, EP⟩ := H.frame hΔ HW hf
  refine ⟨x, hx, HW, ?_, ?_, ?_⟩
  · simpa only [VExpr.inst_eq, VExpr.Subst.one] using HP
  · simpa only [VExpr.inst_eq, VExpr.Subst.one] using ht
  · simpa only [VExpr.inst_eq, VExpr.Subst.one, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using EP

/-- The actual endpoint context when its sole consumed binder is proof-valued.
Identity and the recorded retained-annotation cases need no restriction. -/
inductive ProofEndpointContext (D : Definitions) :
    List ProofShape → List ProofShape → ProofShape.Subst → Prop where
  | identity : ProofEndpointContext D Ξ Ξ ProofShape.Subst.id
  | inst : DomainSort Ξ A .zero → ContextSubstitution (A :: Ξ) Ξ (ProofShape.Subst.one rawX) →
      ProofEndpointContext D (A :: Ξ) Ξ (ProofShape.Subst.one rawX)
  | binder : ScopedCompute (PiInertStage D n) Ξ A A' → ProofEndpointContext D Ξ Ξ' τ →
      ProofEndpointContext D (A :: Ξ) (A'.subst τ :: Ξ') τ.lift

/-- Proof-valued consumption, identity, and every recorded annotation above
it yield an agreeing frame from any chosen source assignment. Retained images
are kept, and their changed domains are handled by actual semantic conversion.
No additional target-image equality is supplied by the caller. -/
theorem ProofEndpointContext.frame
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : ProofEndpointContext D Ξ Ξ' τ)
    (HS : Ctx.SubstEq env univs Δ σ σ Γ) (EΓ : proofEraseCtx Γ = Ξ) :
    ∃ Γ' σ' ρ, proofEraseCtx Γ' = Ξ' ∧ EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ := by
  induction H generalizing Γ σ with
  | identity =>
    exact ⟨Γ, σ, VExpr.Subst.id, EΓ, EqSpecializationFrame.of_conversion hΔ HS (.refl HS.wf)⟩
  | @inst Ξ rawA rawX SD W =>
    cases Γ with
    | nil => cases EΓ
    | cons A Γ =>
      have hΓA := HS.wf
      obtain ⟨EA, EΓ⟩ := List.cons.inj EΓ
      obtain ⟨hΓ, u, hA⟩ := hΓA
      have SD' : DomainSort (proofEraseCtx Γ) rawA .zero := EΓ.symm ▸ SD
      obtain ⟨P, hP, EP⟩ := SD'.realize hΓ
      obtain ⟨_, HPA⟩ := (proofErase_reflect hΓ hP hA (EP.trans EA.symm)).2 (not_isProof_of_sort hΓ hP)
      have hA₀ := ((HPA.defeq hΓ).of_l henv hΓ hP).hasType.2
      have WI : ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx Γ) (ProofShape.Subst.one rawX) := by
        intro Λ hΛ EΛ
        simpa only [EΓ] using W hΛ (by simpa only [proofEraseCtx, EA, EΓ] using EΛ)
      obtain ⟨x, _, _, HW⟩ := WI.proof_supply_frame hΔ HS hA₀
      exact ⟨Γ, σ.tail, VExpr.Subst.one x, EΓ, HW⟩
  | @binder n Ξ rawA rawA' Ξ' τ RD H ih =>
    cases Γ with
    | nil => cases EΓ
    | cons A Γ =>
      have hΓA := HS.wf
      obtain ⟨EA, EΓ⟩ := List.cons.inj EΓ
      cases HS with
      | cons WT hA hy =>
        obtain ⟨A', HA, EA'⟩ := proofErase_scoped_compute_realize
          (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
          WT.wf hA EΓ EA RD
        obtain ⟨Γ', σ', ρ, EΓ', HW⟩ := ih WT EΓ
        have hy' := (HA.subst henv.orderedStrong WT hΔ).defeq hy
        have HL := HW.under_binder hΔ HA.hasType.2 hy'
        have Eσ : σ.tail.cons σ.head = σ := by funext i; cases i <;> rfl
        have HL' : EqSpecializationFrame (A' :: Γ) (A'.subst ρ :: Γ') Δ
            σ (σ'.cons σ.head) ρ.lift τ.lift := by simpa only [Eσ] using HL
        have HC := EqSpecializationFrame.of_conversion hΔ
          (show Ctx.SubstEq env univs Δ σ σ (A :: Γ) from .cons WT hA hy)
          (IsDefEqCtx.succ (.refl WT.wf) HA)
        refine ⟨A'.subst ρ :: Γ', σ'.cons σ.head, ρ.lift, ?_, ?_⟩
        · simp only [proofEraseCtx, proofErase_subst_with HW.target.wf HW.actual HA.hasType.2 HW.erase,
            EA', EΓ']
        · exact HC.compose hΔ HL'

/-- The full proof-endpoint context preserves a chosen Eq specialization,
its whole assigned type, and the exact raw substituted component vector.
The source assignment remains required: arbitrary ambient insertions need
not have images in that target and are handled separately. -/
theorem EqPrefixSpecializationAt.proof_endpoint_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (HC : ProofEndpointContext D (proofEraseCtx Γ) Ξ' τ)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F) :
    ∃ Γ' σ' ρ, proofEraseCtx Γ' = Ξ' ∧ EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ ∧
      EqPrefixSpecializationAt Γ' Δ v w v' w' original (pre.map (·.subst ρ)) σ' pending ∧
      env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map (·.subst ρ))) (F.subst ρ) ∧
      (pre.map (·.subst ρ)).map (proofErase Γ') = (pre.map (proofErase Γ)).map (·.subst τ) := by
  obtain ⟨Γ', σ', ρ, EΓ', HW⟩ := HC.frame heq hs hΔ H.1 rfl
  exact ⟨Γ', σ', ρ, EΓ', HW, H.frame hΔ HW hf⟩

/-- The actual endpoint context either has proof-valued consumption (or is
identity), or retains its particular consumed base binder without a Prop
sort witness. The original base interpretation and exact lifted map remain
in the latter branch; no unrelated substitution is selected. -/
theorem PiInertEndpointContext.proof_or_unwitnessed_domain
    (H : PiInertEndpointContext D Ξ Ξ' τ) :
    ProofEndpointContext D Ξ Ξ' τ ∨
      ∃ Θ A rawX depth, ContextSubstitution (A :: Θ) Θ (ProofShape.Subst.one rawX) ∧
        ¬ DomainSort Θ A .zero ∧ τ = (ProofShape.Subst.one rawX).liftN depth := by
  classical
  induction H with
  | @base source target rawMap H =>
    cases H with
    | identity => exact .inl .identity
    | @inst A _ rawX W =>
      by_cases SD : DomainSort target A .zero
      · exact .inl (.inst SD W)
      · exact .inr ⟨target, A, rawX, 0, W, SD, rfl⟩
  | binder RD _ ih =>
    rcases ih with H | ⟨Θ, A, rawX, depth, W, HN, E⟩
    · exact .inl (.binder RD H)
    · exact .inr ⟨Θ, A, rawX, depth+1, W, HN, congrArg ProofShape.Subst.lift E⟩

/-- At a chosen semantic source realization, the actual recorded endpoint
context either preserves the full specialization and assigned type, or
exposes the exact consumed base binder lacking a Prop-domain witness.
Proof-valued consumption needs no separate target-agreement assumption. -/
theorem EqPrefixSpecializationAt.endpoint_context_frame_or_unwitnessed_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (HC : PiInertEndpointContext D (proofEraseCtx Γ) Ξ' τ)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F) :
    (∃ Γ' σ' ρ, proofEraseCtx Γ' = Ξ' ∧ EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ ∧
      EqPrefixSpecializationAt Γ' Δ v w v' w' original (pre.map (·.subst ρ)) σ' pending ∧
      env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map (·.subst ρ))) (F.subst ρ) ∧
      (pre.map (·.subst ρ)).map (proofErase Γ') = (pre.map (proofErase Γ)).map (·.subst τ)) ∨
      ∃ Θ A rawX depth, ContextSubstitution (A :: Θ) Θ (ProofShape.Subst.one rawX) ∧
        ¬ DomainSort Θ A .zero ∧ τ = (ProofShape.Subst.one rawX).liftN depth := by
  rcases HC.proof_or_unwitnessed_domain with HP | HN
  · exact .inl (H.proof_endpoint_context heq hs hΔ HP hf)
  · exact .inr HN

end Lean4Lean.VEnv.Strengthening
