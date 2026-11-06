import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqChainRetainedSupply

/-! # Chosen supply through a finite retained telescope

Consumption changes insertion offsets. Keep separate source and destination
chains, and relate their erased terms by the actual consumption square.
Computed annotations then extend this square beneath every retained binder.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation

/-- Insertion preserves a lambda and shifts its body path by one binder. -/
theorem EqInsertionPath.erased_lam (blocks : EqInsertionPath) (A body : ProofShape) :
    blocks.erased (.lam A body) = .lam (blocks.erased A) (blocks.underBinder.erased body) := by
  induction blocks generalizing A body with
  | nil => rfl
  | cons p blocks ih =>
    obtain ⟨n,k⟩ := p
    simpa only [EqInsertionPath.erased, ProofShape.liftN,
      EqInsertionPath.underBinder, List.map_cons] using ih (A.liftN n k) (body.liftN n (k+1))

/-- Lift a square between two possibly different insertion paths. This is
necessary when consumption removes a binder above the inserted blocks. -/
theorem EqInsertionPath.square_under_binder
    {incoming outgoing : EqInsertionPath}
    (E : ∀ e : ProofShape, outgoing.erased (e.subst τ) = (incoming.erased e).subst υ) :
    ∀ e : ProofShape, outgoing.underBinder.erased (e.subst τ.lift) =
      (incoming.underBinder.erased e).subst υ.lift := by
  intro e
  have H := E (.lam (.sort .zero) e)
  simp only [ProofShape.subst, EqInsertionPath.erased_lam] at H
  exact (ProofShape.lam.inj H).2

variable [Params]

/-- Retain the source insertions as an identity chain. This forgets only the
old outgoing map, not any inserted declaration, and requires no target image
for an inserted binder. It permits rebuilding an output chain after consumption
has changed its insertion offsets. -/
theorem EqFrameInsertionChain.source_identity
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks) :
    EqFrameInsertionChain Γ Γ VExpr.Subst.id ProofShape.Subst.id
      Λ Λ VExpr.Subst.id ProofShape.Subst.id blocks := by
  induction J with
  | refl => exact .refl
  | step J I ih =>
    apply ih.step
    refine ⟨I.source, I.source, I.actual.wf, Ctx.SubstEq.id henv.ordered I.actual.wf, ?_, ?_, ?_⟩
    · intro i A hl hn
      simp only [VExpr.Subst.id, ProofShape.Subst.id, proofErase, if_neg hn]
    · intro e; simp only [VExpr.subst_id]
    · intro e; simp only [ProofShape.subst_id]

/-- Actual annotation histories above one already supplied scope change.
Every newer binder retains its chosen image and original source annotation.
Its counted native annotation path and actual lambda wrapper are recorded
before the older map acts; no path is substituted and no later chosen-image
agreement is postulated. The base scope
change is supplied separately by the actual consumed-argument history. -/
inductive EqRetainedSupplyHistory (D : Definitions) (Δ Γ₀ Λ₀ : List VExpr)
    (σ₀ : VExpr.Subst) (blocks₀ : EqInsertionPath) (Ψ₀ : List ProofShape)
    (υ₀ : ProofShape.Subst) :
    List VExpr → List VExpr → VExpr.Subst → EqInsertionPath →
    List ProofShape → ProofShape.Subst → (ProofShape → ProofShape) → Nat → Prop where
  | base : EqRetainedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀ id 0
  | binder : EqRetainedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀ Γ Λ σ blocks Ψ υ plug depth →
      env.HasType univs Γ A (.sort u) → env.HasType univs Δ y (A.subst σ) →
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ)
        (blocks.erased (proofErase Γ A)) rawA' →
      EqRetainedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
        (A :: Γ) (blocks.actual A :: Λ) (σ.cons y) blocks.underBinder
        (rawA'.subst υ :: Ψ) υ.lift
        (fun e => plug (ProofShape.mkApps (.lam rawA' e) args)) (depth+1)

/-- The history shifts every original insertion and the exact raw base map
once per retained binder; neither path can acquire an unrelated offset. -/
theorem EqRetainedSupplyHistory.shape
    (H : EqRetainedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀ Γ Λ σ blocks Ψ υ plug depth) :
    blocks = blocks₀.underBinders depth ∧ υ = υ₀.liftN depth := by
  induction H with
  | base =>
    constructor
    · simp only [EqInsertionPath.underBinders, Nat.add_zero, List.map_id_fun', id_eq]
    · rfl
  | binder _ _ _ _ ih =>
    obtain ⟨rfl, rfl⟩ := ih
    refine ⟨?_, rfl⟩
    simp only [EqInsertionPath.underBinder, EqInsertionPath.underBinders,
      List.map_map, Function.comp_def, Nat.add_assoc]

/-- Forget chosen images only after checking the actual source scopes.
The result is the native endpoint-context history used by retained-frame
execution, with exactly the original annotation computations. -/
theorem EqRetainedSupplyHistory.endpoint
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqRetainedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀ Γ Λ σ blocks Ψ υ plug depth)
    (S : Ctx.SubstEq env univs Δ σ₀ σ₀ Γ₀)
    (J : EqFrameInsertionChain Γ₀ Γ₀ VExpr.Subst.id ProofShape.Subst.id
      Λ₀ Λ₀ VExpr.Subst.id ProofShape.Subst.id blocks₀)
    (HC : PiInertEndpointContext D (proofEraseCtx Λ₀) Ψ₀ υ₀) :
    Ctx.SubstEq env univs Δ σ σ Γ ∧
      EqFrameInsertionChain Γ Γ VExpr.Subst.id ProofShape.Subst.id
        Λ Λ VExpr.Subst.id ProofShape.Subst.id blocks ∧
      PiInertEndpointContext D (proofEraseCtx Λ) Ψ υ := by
  induction H with
  | base => exact ⟨S, J, HC⟩
  | @binder Γ Λ σ blocks Ψ υ plug depth A u y n cd rawA' args H hA hy RD ih =>
    obtain ⟨S, J, HC⟩ := ih
    have W := EqSpecializationFrame.of_conversion hΔ S (.refl S.wf)
    refine ⟨.cons S hA hy, ?_, ?_⟩
    · simpa only [VExpr.id_lift, ProofShape.Subst.id_lift, VExpr.subst_id] using J.under_binder W hA
    · simpa only [proofEraseCtx, J.erase_actual W hA] using PiInertEndpointContext.binder RD.forget HC

/-- Realize any finite retained annotation history over an agreeing base map.
Separate identity insertion chains survive on both sides, while an agreeing
specialization frame carries all chosen images. The raw outgoing context and
commuting square are exact, including all computed annotations. -/
theorem EqRetainedSupplyHistory.realize
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqRetainedSupplyHistory D Δ Γ₀ Λ₀ σ₀ incoming Ψ₀ υ₀ Γ Λ σ blocks Ψ υ plug depth)
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ₀ τ₀)
    (JS : EqFrameInsertionChain Γ₀ Γ₀ VExpr.Subst.id ProofShape.Subst.id
      Λ₀ Λ₀ VExpr.Subst.id ProofShape.Subst.id incoming)
    (JT : EqFrameInsertionChain Γ₀' Γ₀' VExpr.Subst.id ProofShape.Subst.id
      Λ₀' Λ₀' VExpr.Subst.id ProofShape.Subst.id outgoing)
    (EΨ : Ψ₀ = proofEraseCtx Λ₀')
    (ES : ∀ e : ProofShape, outgoing.erased (e.subst τ₀) = (incoming.erased e).subst υ₀) :
    ∃ (Γ' Λ' : List VExpr) (σ' : VExpr.Subst) (outblocks : EqInsertionPath),
      EqSpecializationFrame Γ Γ' Δ σ σ' (ρ₀.liftN depth) (τ₀.liftN depth) ∧
      EqFrameInsertionChain Γ Γ VExpr.Subst.id ProofShape.Subst.id
        Λ Λ VExpr.Subst.id ProofShape.Subst.id blocks ∧
      EqFrameInsertionChain Γ' Γ' VExpr.Subst.id ProofShape.Subst.id
        Λ' Λ' VExpr.Subst.id ProofShape.Subst.id outblocks ∧
      Ψ = proofEraseCtx Λ' ∧
      (∀ e : ProofShape, outblocks.erased (e.subst (τ₀.liftN depth)) = (blocks.erased e).subst υ) ∧
      outblocks = outgoing.underBinders depth := by
  induction H with
  | base =>
    refine ⟨Γ₀', Λ₀', σ₀', outgoing, W, JS, JT, EΨ, ES, ?_⟩
    simp only [EqInsertionPath.underBinders, Nat.add_zero, List.map_id_fun', id_eq]
  | @binder Γ Λ σ blocks Ψ υ plug depth A u y n cd rawA' args H hA hy RD ih =>
    obtain ⟨Γ', Λ', σ', outblocks, WF, JS, JT, EΨ, ES, Eblocks⟩ := ih
    have WS := EqSpecializationFrame.of_conversion hΔ WF.agree.left (.refl WF.actual.wf)
    have WT := EqSpecializationFrame.of_conversion hΔ WF.target (.refl WF.target.wf)
    obtain ⟨B, HAB, RB, EB⟩ := JS.compute_certificate
      (pi_inert_stage_certificate_descent heq hs n) WS hA RD.forget
    have C : IsDefEqCtx env univs []
        (A.subst (ρ₀.liftN depth) :: Γ') (B.subst (ρ₀.liftN depth) :: Γ') :=
      .succ (.refl WF.target.wf) (HAB.subst henv.orderedStrong WF.actual WF.target.wf)
    have Wnew := (WF.under_binder hΔ hA hy).target_convert hΔ C
    have hBout : env.HasType univs Γ' (B.subst (ρ₀.liftN depth)) (.sort u) := by
      simpa only [VExpr.subst] using HAB.hasType.2.subst henv.orderedStrong WF.actual WF.target.wf
    have JSnew := JS.under_binder WS hA
    have JTnew := JT.under_binder WT hBout
    have Eout : proofErase Λ' (outblocks.actual (B.subst (ρ₀.liftN depth))) = rawA'.subst υ := by
      rw [JT.erase_actual WT hBout, proofErase_subst_with WF.target.wf WF.actual HAB.hasType.2 WF.erase,
        ES, EB]
    refine ⟨_, outblocks.actual (B.subst (ρ₀.liftN depth)) :: Λ', σ'.cons y, outblocks.underBinder, Wnew, ?_, ?_, ?_,
      EqInsertionPath.square_under_binder ES, ?_⟩
    · simpa only [VExpr.id_lift, ProofShape.Subst.id_lift, VExpr.subst_id] using JSnew
    · simpa only [VExpr.id_lift, ProofShape.Subst.id_lift, VExpr.subst_id] using JTnew
    · simp only [proofEraseCtx, ← EΨ, Eout]
    · simp only [Eblocks, EqInsertionPath.underBinder, EqInsertionPath.underBinders,
        List.map_map, Function.comp_def, Nat.add_assoc]


/-- Read a nonempty recorded retained telescope from the actual whole suffix
minimum. Each lambda readout uses its own selected suffix and adds exactly one
frame; the older application is not reintroduced. This derives the inner
minimum at the exact context and map already used by supply realization. -/
theorem EqRetainedSupplyHistory.focus_nonempty
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : EqRetainedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀ Γ Λ σ blocks Ψ υ plug depth)
    (hd : 0 < depth)
    (HM : PiInertFrameMinimum D Ω out Ψ₀
      (ProofShape.mkApps ((plug e).subst υ₀) pending) cost frames) :
    ∃ smaller, smaller ≤ cost ∧
      PiInertFrameMinimum D Ω out Ψ (e.subst υ) smaller (frames+depth) := by
  induction H generalizing e pending cost frames with
  | base => omega
  | @binder Γ Λ σ blocks Ψ υ plug depth A u y n cd rawA' args H hA hy RD ih =>
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

/-- An actual computed older argument supplies the base agreement for every
retained binder above it. Its native path determines the lower argument; both
insertion paths, all chosen images, and the actual outgoing raw context survive.
This generalizes consumption beneath one unchanged annotation to any finite
history of computed annotations. -/
theorem EqRetainedSupplyHistory.consume
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (harg : ErasedScopedPrimitiveCertificateDescent ArgStep ArgStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω incoming)
    (hA : env.HasType univs Γ₀ A (.sort u)) (hx : env.HasType univs Γ₀ x A)
    (RX : ScopedCompute ArgStep (proofEraseCtx Λ₀) (incoming.erased (proofErase Γ₀ x)) rawX)
    (H : EqRetainedSupplyHistory D Δ (A :: Γ₀) (incoming.actual A :: Λ₀)
      (σ₀.cons (x.subst σ₀)) incoming.underBinder (proofEraseCtx Λ₀)
      (ProofShape.Subst.one rawX) Γ Λ σ blocks Ψ υ plug depth) :
    ∃ (x' : VExpr) (Γ' Λ' : List VExpr) (σ' : VExpr.Subst),
      env.IsDefEq univs Γ₀ x x' A ∧ incoming.erased (proofErase Γ₀ x') = rawX ∧
      EqSpecializationFrame Γ Γ' Δ σ σ' ((VExpr.Subst.one x').liftN depth)
        ((ProofShape.Subst.one (proofErase Γ₀ x')).liftN depth) ∧
      EqFrameInsertionChain Γ Γ VExpr.Subst.id ProofShape.Subst.id
        Λ Λ VExpr.Subst.id ProofShape.Subst.id blocks ∧
      EqFrameInsertionChain Γ' Γ' VExpr.Subst.id ProofShape.Subst.id
        Λ' Λ' VExpr.Subst.id ProofShape.Subst.id (incoming.underBinders depth) ∧
      Ψ = proofEraseCtx Λ' ∧
      (∀ e : ProofShape, (incoming.underBinders depth).erased
        (e.subst ((ProofShape.Subst.one (proofErase Γ₀ x')).liftN depth)) =
        (blocks.erased e).subst υ) := by
  obtain ⟨x', HX, _, EX⟩ := J.compute_certificate harg W hx RX
  have WI := EqSpecializationFrame.inst W.agree.left hA HX.hasType.2
    (HX.subst henv.orderedStrong W.agree.left hΔ)
  have W₀ := EqSpecializationFrame.of_conversion hΔ W.agree.left (.refl W.actual.wf)
  have JS := J.source_identity.under_binder W₀ hA
  have JS : EqFrameInsertionChain (A :: Γ₀) (A :: Γ₀) VExpr.Subst.id ProofShape.Subst.id
      (incoming.actual A :: Λ₀) (incoming.actual A :: Λ₀)
      VExpr.Subst.id ProofShape.Subst.id incoming.underBinder := by
    simpa only [VExpr.id_lift, ProofShape.Subst.id_lift, VExpr.subst_id] using JS
  have ES : ∀ e : ProofShape, incoming.erased (e.subst (ProofShape.Subst.one (proofErase Γ₀ x'))) =
      (incoming.underBinder.erased e).subst (ProofShape.Subst.one rawX) := by
    intro e
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, EX] using
      incoming.erased_inst e (proofErase Γ₀ x')
  obtain ⟨Γ', Λ', σ', outblocks, WF, JS, JT, EΨ, ES, rfl⟩ :=
    H.realize heq hs hΔ WI JS J.source_identity rfl ES
  exact ⟨x', Γ', Λ', σ', HX, EX, WF, JS, JT, EΨ, ES⟩

open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

/-- Lower a component-only body, execute its older supplied consumption below
the entire retained telescope, and return to the same chosen-chain minimum
class. The given minimum is the actual suffix at the substituted raw body;
its cost and unrestricted competitors are retained exactly. The remaining
global obligation is to construct this history at every nested cut and connect
that suffix to the parent minimum, rather than assume future agreement. -/
theorem EqPrefixSpecializationAt.retained_telescope_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hbody : ErasedScopedPrimitiveCertificateDescent BodyStep BodyStep)
    (harg : ErasedScopedPrimitiveCertificateDescent ArgStep ArgStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω incoming)
    (hA : env.HasType univs Γ₀ A (.sort u)) (hx : env.HasType univs Γ₀ x A)
    (RX : ScopedCompute ArgStep (proofEraseCtx Λ₀) (incoming.erased (proofErase Γ₀ x)) rawX)
    (HH : EqRetainedSupplyHistory D Δ (A :: Γ₀) (incoming.actual A :: Λ₀)
      (σ₀.cons (x.subst σ₀)) incoming.underBinder (proofEraseCtx Λ₀)
      (ProofShape.Subst.one rawX) Γ Λ σ blocks Ψ υ plug depth)
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx Λ))
      ((pre.map (proofErase Γ)).map blocks.erased) rawBody)
    (hextra : extra = [] ∨ pending = [])
    (HM : PiInertTypedContinuationMinimum D Ω out Ψ
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (rawBody.map (·.subst υ) ++ extra)) cost) :
    ∃ (x' : VExpr) (Γ' Λ' : List VExpr) (σ' : VExpr.Subst) (final : List VExpr),
      env.IsDefEq univs Γ₀ x x' A ∧ incoming.erased (proofErase Γ₀ x') = rawX ∧
      EqPrefixSpecializationAt Γ' Δ v w v'' w'' original final σ' pending ∧
      env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) final)
        (F.subst ((VExpr.Subst.one x').liftN depth)) ∧
      ¬ IsProof Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) final) ∧
      Ψ = proofEraseCtx Λ' ∧
      ((final.map (proofErase Γ')).map (incoming.underBinders depth).erased) = rawBody.map (·.subst υ) ∧
      PiInertTypedContinuationMinimum D Ω out (proofEraseCtx Λ')
        (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
          (((final.map (proofErase Γ')).map (incoming.underBinders depth).erased) ++ extra)) cost ∧
      EqChainContinuationMinimum D Δ v w original Ω out cost := by
  obtain ⟨x', Γ', Λ', σ', HX, EX, WF, JS, JT, EΨ, ES⟩ :=
    HH.consume heq hs harg hΔ W J hA hx RX
  have WS := EqSpecializationFrame.of_conversion hΔ WF.agree.left (.refl WF.actual.wf)
  obtain ⟨pre', HP, _, _, Ebody, _, HE⟩ := H.compute_insertion_chain hbody hΔ WS JS hf HC HA
  obtain ⟨Hout, hout, Eout⟩ := HP.frame hΔ WF HE.hasType.2
  have hnout : ¬ IsProof Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w''])
      (pre'.map (·.subst ((VExpr.Subst.one x').liftN depth)))) := by
    intro hp
    apply hn ((isProof_congr H.1.wf HE).2 ?_)
    apply (isProof_subst WF.target.wf WF.actual HE.hasType.2).1
    simpa only [VExpr.subst_mkApps, VExpr.subst] using hp
  have Efinal : (((pre'.map (·.subst ((VExpr.Subst.one x').liftN depth))).map (proofErase Γ')).map
      (incoming.underBinders depth).erased) = rawBody.map (·.subst υ) := by
    rw [Eout, ← Ebody]
    simp only [List.map_map, Function.comp_def, ES]
  have HMout : PiInertTypedContinuationMinimum D Ω out (proofEraseCtx Λ')
      (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
        (((pre'.map (·.subst ((VExpr.Subst.one x').liftN depth))).map (proofErase Γ') |>.map
          (incoming.underBinders depth).erased) ++ extra)) cost := by
    simpa only [Efinal, ← EΨ] using HM
  refine ⟨x', Γ', Λ', σ', _, HX, EX, Hout, hout, hnout, EΨ, Efinal, HMout, ?_⟩
  have WT := EqSpecializationFrame.of_conversion hΔ WF.target (.refl WF.target.wf)
  exact ⟨Γ', Γ', Λ', Λ', σ', σ', VExpr.Subst.id, ProofShape.Subst.id,
    VExpr.Subst.id, ProofShape.Subst.id, incoming.underBinders depth, v'', w'', _, pending, extra, _,
    Hout, WT, JT, hout, hnout, hextra, HMout⟩


/-- Execute the whole retained suffix before returning its supplied body to
the chosen-chain class. Unlike `retained_telescope_return`, this does not assume
an inner body minimum: it derives that minimum from the recorded wrappers and
the actual whole minimum. Primitive cost does not increase; the resulting run
has one frame per retained binder over the selected suffix, with no rebuilt
older application frame. Deriving the history from every nested cut remains
outside this theorem. -/
theorem EqPrefixSpecializationAt.retained_telescope_whole_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hbody : ErasedScopedPrimitiveCertificateDescent BodyStep BodyStep)
    (harg : ErasedScopedPrimitiveCertificateDescent ArgStep ArgStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω incoming)
    (hA : env.HasType univs Γ₀ A (.sort u)) (hx : env.HasType univs Γ₀ x A)
    (RX : ScopedCompute ArgStep (proofEraseCtx Λ₀) (incoming.erased (proofErase Γ₀ x)) rawX)
    (HH : EqRetainedSupplyHistory D Δ (A :: Γ₀) (incoming.actual A :: Λ₀)
      (σ₀.cons (x.subst σ₀)) incoming.underBinder (proofEraseCtx Λ₀)
      (ProofShape.Subst.one rawX) Γ Λ σ blocks Ψ υ plug depth)
    (hd : 0 < depth)
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx Λ))
      ((pre.map (proofErase Γ)).map blocks.erased) rawBody)
    (HM : PiInertFrameMinimum D Ω out (proofEraseCtx Λ₀)
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawBody)).subst
        (ProofShape.Subst.one rawX)) outerArgs) cost frames) :
    ∃ smaller, smaller ≤ cost ∧
      PiInertFrameMinimum D Ω out Ψ
        (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (rawBody.map (·.subst υ)))
        smaller (frames+depth) ∧
      EqChainContinuationMinimum D Δ v w original Ω out smaller := by
  obtain ⟨smaller, hsmall, HB⟩ := HH.focus_nonempty heq hs hd HM
  have HB : PiInertFrameMinimum D Ω out Ψ
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (rawBody.map (·.subst υ)))
      smaller (frames+depth) := by
    simpa only [ProofShape.subst_mkApps, ProofShape.subst] using HB
  obtain ⟨x', Γ', Λ', σ', final, HX, EX, HP, ht, hnout, EΨ, Efinal, HMout, Hchain⟩ :=
    H.retained_telescope_return heq hs hbody harg hΔ W J hA hx RX HH hf hn HC HA
      (extra := []) (.inl rfl) (by simpa only [List.append_nil] using HB.forget)
  exact ⟨smaller, hsmall, HB, Hchain⟩

/-- Resume the actual selected application suffix through the entire retained
telescope. The parent predicate and counted body path derive the whole suffix
minimum, so neither whole nor inner minima are separate premises. If primitive
cost is unchanged, exactly the older application frame is removed relative to
the recorded depth-plus-application prefix. The remaining global gap is carrying
the supplied telescope history to every such selected continuation. -/
theorem EqPrefixSpecializationAt.retained_telescope_selected_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hbody : ErasedScopedPrimitiveCertificateDescent BodyStep BodyStep)
    (harg : ErasedScopedPrimitiveCertificateDescent ArgStep ArgStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω incoming)
    (hA : env.HasType univs Γ₀ A (.sort u)) (hx : env.HasType univs Γ₀ x A)
    (RX : ScopedCompute ArgStep (proofEraseCtx Λ₀) (incoming.erased (proofErase Γ₀ x)) rawX)
    (HH : EqRetainedSupplyHistory D Δ (A :: Γ₀) (incoming.actual A :: Λ₀)
      (σ₀.cons (x.subst σ₀)) incoming.underBinder (proofEraseCtx Λ₀)
      (ProofShape.Subst.one rawX) Γ Λ σ blocks Ψ υ plug depth)
    (hd : 0 < depth)
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx Λ))
      ((pre.map (proofErase Γ)).map blocks.erased) rawBody)
    (RP : ScopedComputeCount (PiInertStage D n) cb (proofEraseCtx Λ) source
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawBody))
    (HTnext : TypedSource (proofEraseCtx Λ₀)
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawBody)).subst
        (ProofShape.Subst.one rawX)) outerArgs))
    (RT : ScopedComputeCount (PiInertStage D m) cs (proofEraseCtx Λ₀)
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawBody)).subst
        (ProofShape.Subst.one rawX)) outerArgs) endpoint)
    (HK : PiInertRunFrames D Ω out (proofEraseCtx Λ₀) K endpoint ck frames)
    (hc : cb+(cs+ck) = cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Λ) source tail →
      PiInertApplicationContinuation D (proofEraseCtx Λ₀) (ProofShape.Subst.one rawX) outerArgs K
        (plug tail) k → cost ≤ j+k) :
    ∃ smaller, smaller ≤ cs+ck ∧
      PiInertFrameMinimum D Ω out Ψ
        (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (rawBody.map (·.subst υ)))
        smaller (frames+depth) ∧
      EqChainContinuationMinimum D Δ v w original Ω out smaller ∧
      (smaller < cost ∨ smaller = cost ∧ frames+depth < frames+depth+1) := by
  have HMnext : PiInertFrameMinimum D Ω out (proofEraseCtx Λ₀)
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawBody)).subst
        (ProofShape.Subst.one rawX)) outerArgs) (cs+ck) frames := by
    refine ⟨K, m, cs, ck, endpoint, HTnext, RT, HK, rfl, ?_⟩
    intro later j tail k RJ HL
    have HB := HM n cb _ (j+k) RP ⟨later, j, tail, k, rfl, RJ, HL⟩
    omega
  obtain ⟨smaller, hsmall, HB, Hchain⟩ := H.retained_telescope_whole_return
    heq hs hbody harg hΔ W J hA hx RX HH hd hf hn HC HA HMnext
  exact ⟨smaller, hsmall, HB, Hchain, by omega⟩

end Lean4Lean.VEnv.Strengthening
