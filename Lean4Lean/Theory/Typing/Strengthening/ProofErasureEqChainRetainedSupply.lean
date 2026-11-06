import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqChainSupply
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress

/-! # Consume an older supplied argument beneath a retained binder

Nested eta can open a new binder before the continuation consumes an older
supplied argument. The older argument's actual component path determines the
lifted consumption map. Its agreement preserves the newer chosen image;
that image need not be the specialization of the older argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

/-- Move every insertion beneath a finite retained prefix. -/
def EqInsertionPath.underBinders (blocks : EqInsertionPath) (depth : Nat) : EqInsertionPath :=
  blocks.map fun (n,k) => (n,k+depth)

/-- Consumption at any retained depth commutes with the ordered insertion
path. The source and destination insertion offsets differ by one; the actual
argument follows the original path below the entire retained prefix. -/
theorem EqInsertionPath.erased_instN (blocks : EqInsertionPath) (body x : ProofShape) (depth : Nat) :
    (blocks.underBinders depth).erased (body.inst x depth) =
      ((blocks.underBinders (depth+1)).erased body).inst (blocks.erased x) depth := by
  induction blocks generalizing body x with
  | nil => rfl
  | cons p blocks ih =>
    obtain ⟨n,k⟩ := p
    change (EqInsertionPath.underBinders blocks depth).erased ((body.inst x depth).liftN n (k+depth)) = _
    rw [ProofShape.liftN_instN]
    simpa only [EqInsertionPath.underBinders, List.map_cons, EqInsertionPath.erased,
      Nat.add_assoc] using ih (body.liftN n (k+depth+1)) (x.liftN n k)

/-- One retained binder leaves the actual consumption map lifted once. -/
theorem EqInsertionPath.erased_retained_inst (blocks : EqInsertionPath) (body x : ProofShape) :
    blocks.underBinder.erased (body.subst (ProofShape.Subst.one x).lift) =
      (blocks.underBinder.underBinder.erased body).subst
        (ProofShape.Subst.one (blocks.erased x)).lift := by
  have E : blocks.underBinders 2 = blocks.underBinder.underBinder := by
    simp only [EqInsertionPath.underBinders, EqInsertionPath.underBinder, List.map_map,
      Function.comp_def, Nat.add_assoc]
  simpa only [show blocks.underBinders 1 = blocks.underBinder from rfl, E,
    ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using blocks.erased_instN body x 1

variable [Params]

/-- Descend the actual body and older supplied argument through their own
insertion paths, then consume that argument beneath a newer retained binder.
The newer chosen image and all pending target arguments survive unchanged.
Both the exact upper lifted map and its outgoing component vector are derived;
agreement with an arbitrary future argument is not a premise or conclusion.
Linking this local step to the continuation's original supply history remains
necessary for the general empty-suffix frontier. -/
theorem EqPrefixSpecializationAt.chain_retained_supplied_components
    (hbody : ErasedScopedPrimitiveCertificateDescent BodyStep BodyStep)
    (harg : ErasedScopedPrimitiveCertificateDescent ArgStep ArgStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt (B :: A :: Γ) Δ v w v' w' original pre
      ((σ.cons (x.subst σ)).cons y) pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x A)
    (hB : env.HasType univs (A :: Γ) B (.sort z))
    (hy : env.HasType univs Δ y (B.subst (σ.cons (x.subst σ))))
    (hf : env.HasType univs (B :: A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof (B :: A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : env.IsDefEqU univs (B :: A :: Γ) (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep
      (proofEraseCtx (blocks.underBinder.actual B :: blocks.actual A :: Λ)))
      ((pre.map (proofErase (B :: A :: Γ))).map blocks.underBinder.underBinder.erased) rawBody)
    (RX : ScopedCompute ArgStep (proofEraseCtx Λ) (blocks.erased (proofErase Γ x)) rawX) :
    ∃ (pre' : List VExpr) (x' : VExpr), env.IsDefEq univs Γ x x' A ∧
      blocks.erased (proofErase Γ x') = rawX ∧
      EqSpecializationFrame (B :: A :: Γ) (B.inst x' :: Γ) Δ
        ((σ.cons (x.subst σ)).cons y) (σ.cons y)
        (VExpr.Subst.one x').lift (ProofShape.Subst.one (proofErase Γ x')).lift ∧
      proofErase Λ (blocks.actual (B.inst x')) =
        (proofErase (blocks.actual A :: Λ) (blocks.underBinder.actual B)).inst rawX ∧
      ContextSubstitution
        (proofEraseCtx (blocks.underBinder.actual B :: blocks.actual A :: Λ))
        (proofEraseCtx (blocks.actual (B.inst x') :: Λ)) (ProofShape.Subst.one rawX).lift ∧
      EqPrefixSpecializationAt (B.inst x' :: Γ) Δ v w v'' w'' original
        (pre'.map (·.subst (VExpr.Subst.one x').lift)) (σ.cons y) pending ∧
      env.HasType univs (B.inst x' :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.subst (VExpr.Subst.one x').lift)))
        (F.subst (VExpr.Subst.one x').lift) ∧
      ¬ IsProof (B.inst x' :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.subst (VExpr.Subst.one x').lift))) ∧
      (((pre'.map (·.subst (VExpr.Subst.one x').lift)).map (proofErase (B.inst x' :: Γ))).map
        blocks.underBinder.erased) = rawBody.map (·.subst (ProofShape.Subst.one rawX).lift) := by
  have hxσ := hx.subst henv.orderedStrong W.agree.left hΔ
  have WF := W.under_binder hΔ hA hxσ
  have JF := J.under_binder W hA
  have WFF := WF.under_binder hΔ hB hy
  have JFF := JF.under_binder WF hB
  obtain ⟨pre', HP, _, _, Ebody, _, HE⟩ := H.compute_insertion_chain hbody hΔ WFF JFF hf HC HA
  obtain ⟨x', HX, _, EX⟩ := J.compute_certificate harg W hx RX
  have WI := EqSpecializationFrame.inst W.agree.left hA HX.hasType.2
    (HX.subst henv.orderedStrong W.agree.left hΔ)
  have WR : EqSpecializationFrame (B :: A :: Γ) (B.inst x' :: Γ) Δ
      ((σ.cons (x.subst σ)).cons y) (σ.cons y)
      (VExpr.Subst.one x').lift (ProofShape.Subst.one (proofErase Γ x')).lift := by
    simpa only [VExpr.inst_eq] using WI.under_binder hΔ hB hy
  obtain ⟨HPi, hpi, Epi⟩ := HP.frame hΔ WR HE.hasType.2
  have hni : ¬ IsProof (B.inst x' :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.subst (VExpr.Subst.one x').lift))) := by
    intro hp
    have hnpre := fun hp => hn ((isProof_congr H.1.wf HE).2 hp)
    apply hnpre ((isProof_subst WR.target.wf WR.actual HE.hasType.2).1 ?_)
    simpa only [VExpr.subst_mkApps, VExpr.subst] using hp
  have EI : (((pre'.map (·.subst (VExpr.Subst.one x').lift)).map (proofErase (B.inst x' :: Γ))).map
      blocks.underBinder.erased) = rawBody.map (·.subst (ProofShape.Subst.one rawX).lift) := by
    rw [Epi, ← Ebody, ← EX]
    simp only [List.map_map, Function.comp_def, EqInsertionPath.erased_retained_inst]
  have EB : blocks.erased (proofErase Γ (B.inst x')) =
      (blocks.underBinder.erased (proofErase (A :: Γ) B)).inst rawX := by
    have E := proofErase_subst_with WI.target.wf WI.actual hB WI.erase
    have E : proofErase Γ (B.inst x') = (proofErase (A :: Γ) B).inst (proofErase Γ x') := by
      simpa only [VExpr.inst_eq, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using E
    rw [E, EqInsertionPath.erased_inst, EX]
  obtain ⟨_, S, _⟩ := J.actual W
  have hAup : env.HasType univs Λ (blocks.actual A) (.sort u) := by
    simpa only [EqInsertionPath.actual_sort] using J.weak hA
  have hΛA : OnCtx (blocks.actual A :: Λ) (env.IsType univs) := ⟨S.wf, u, hAup⟩
  have EXup : proofErase Λ (blocks.actual x') = rawX := (J.erase_actual W HX.hasType.2).trans EX
  have WX : ContextSubstitution (proofEraseCtx (blocks.actual A :: Λ)) (proofEraseCtx Λ)
      (ProofShape.Subst.one rawX) := by
    have WX : ContextSubstitution (proofEraseCtx (blocks.actual A :: Λ)) (proofEraseCtx Λ)
        (ProofShape.Subst.one (proofErase Λ (blocks.actual x'))) := ContextSubstitution.of_typed S.wf (Ctx.InstN.zero.substEq hΛA (J.weak HX.hasType.2))
      (erasedSubstAgreement_one hΛA (J.weak HX.hasType.2))
    intro Ψ hΨ EΨ
    simpa only [EXup] using WX hΨ EΨ
  have hBi : env.HasType univs Γ (B.inst x') (.sort z) := by
    simpa only [VExpr.inst_eq, VExpr.subst] using hB.subst henv.orderedStrong WI.actual WI.target.wf
  have EBup : proofErase Λ (blocks.actual (B.inst x')) =
      (proofErase (blocks.actual A :: Λ) (blocks.underBinder.actual B)).subst
        (ProofShape.Subst.one rawX) := by
    rw [J.erase_actual W hBi, JF.erase_actual WF hB]
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using EB
  refine ⟨pre', x', HX, EX, WR, (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using EBup), ?_, HPi, hpi, hni, EI⟩
  intro Ψ hΨ EΨ
  simpa only [proofEraseCtx, EBup] using
    ContextSubstitution.cons (A := proofErase (blocks.actual A :: Λ) (blocks.underBinder.actual B)) WX hΨ EΨ

/-- Execute the actual enclosing retained-lambda/older-consumption pair and
read the selected suffix back at its substituted body. The preserved chosen
specialization and the new minimum refer to that exact body and scope. The
suffix's actual pending arguments and continuation are kept when constructing
the minimum; one frame over that suffix replaces the displayed pair. This
handles an older supplied argument beneath one unchanged retained annotation,
not arbitrary supply ancestry or an arbitrary retained-prefix history. -/
theorem EqPrefixSpecializationAt.chain_retained_supplied_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hbody : ErasedScopedPrimitiveCertificateDescent BodyStep BodyStep)
    (harg : ErasedScopedPrimitiveCertificateDescent ArgStep ArgStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt (B :: A :: Γ) Δ v w v' w' original pre
      ((σ.cons (x.subst σ)).cons y) pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x A)
    (hB : env.HasType univs (A :: Γ) B (.sort z))
    (hy : env.HasType univs Δ y (B.subst (σ.cons (x.subst σ))))
    (hf : env.HasType univs (B :: A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof (B :: A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : env.IsDefEqU univs (B :: A :: Γ) (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep
      (proofEraseCtx (blocks.underBinder.actual B :: blocks.actual A :: Λ)))
      ((pre.map (proofErase (B :: A :: Γ))).map blocks.underBinder.underBinder.erased) rawBody)
    (RX : ScopedCompute ArgStep (proofEraseCtx Λ) (blocks.erased (proofErase Γ x)) rawX)
    (RP : ScopedComputeCount (PiInertStage D n) cb
      (proofEraseCtx (blocks.underBinder.actual B :: blocks.actual A :: Λ)) source
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawBody))
    (HTnext : TypedSource (proofEraseCtx Λ)
      (ProofShape.mkApps (.lam
        ((proofErase (blocks.actual A :: Λ) (blocks.underBinder.actual B)).inst rawX)
        (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
          (rawBody.map (·.subst (ProofShape.Subst.one rawX).lift)))) args))
    (RT : ScopedComputeCount (PiInertStage D m) cs (proofEraseCtx Λ)
      (ProofShape.mkApps (.lam
        ((proofErase (blocks.actual A :: Λ) (blocks.underBinder.actual B)).inst rawX)
        (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
          (rawBody.map (·.subst (ProofShape.Subst.one rawX).lift)))) args) endpoint)
    (HK : PiInertRunFrames D Ω out (proofEraseCtx Λ) K endpoint ck frames)
    (hc : cb+(cs+ck) = cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j
      (proofEraseCtx (blocks.underBinder.actual B :: blocks.actual A :: Λ)) source tail →
      PiInertApplicationContinuation D (proofEraseCtx Λ) (ProofShape.Subst.one rawX) args K
        (.lam (proofErase (blocks.actual A :: Λ) (blocks.underBinder.actual B)) tail) k → cost ≤ j+k) :
    ∃ (x' : VExpr) (final : List VExpr) (smaller : Nat),
      env.IsDefEq univs Γ x x' A ∧
      EqPrefixSpecializationAt (B.inst x' :: Γ) Δ v w v'' w'' original final (σ.cons y) pending ∧
      env.HasType univs (B.inst x' :: Γ) (VExpr.mkApps (.const ``Eq.rec [v'',w'']) final)
        (F.subst (VExpr.Subst.one x').lift) ∧
      ¬ IsProof (B.inst x' :: Γ) (VExpr.mkApps (.const ``Eq.rec [v'',w'']) final) ∧
      ((final.map (proofErase (B.inst x' :: Γ))).map blocks.underBinder.erased) =
        rawBody.map (·.subst (ProofShape.Subst.one rawX).lift) ∧
      PiInertFrameMinimum D Ω out (proofEraseCtx (blocks.actual (B.inst x') :: Λ))
        (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
          ((final.map (proofErase (B.inst x' :: Γ))).map blocks.underBinder.erased)) smaller (frames+1) ∧
      EqChainContinuationMinimum D Δ v w original Ω out smaller ∧
      smaller ≤ cs+ck ∧ (smaller < cost ∨ smaller = cost ∧ frames+1 < frames+2) := by
  obtain ⟨pre', x', HX, _, _, EB, _, HP, hpi, hni, EI⟩ :=
    H.chain_retained_supplied_components hbody harg hΔ W J hA hx hB hy hf hn HC HA RX
  have HMnext : PiInertFrameMinimum D Ω out (proofEraseCtx Λ)
      (ProofShape.mkApps (.lam
        ((proofErase (blocks.actual A :: Λ) (blocks.underBinder.actual B)).inst rawX)
        (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
          (rawBody.map (·.subst (ProofShape.Subst.one rawX).lift)))) args) (cs+ck) frames := by
    refine ⟨K, m, cs, ck, endpoint, HTnext, RT, HK, rfl, ?_⟩
    intro later j tail k RJ HL
    have HH := HM n cb _ (j+k) RP ⟨later, j, tail, k, rfl, ?_, HL⟩
    · omega
    · simpa only [ProofShape.subst, ProofShape.subst_mkApps,
        ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RJ
  obtain ⟨smaller, hsmall, HMbody⟩ := HMnext.lambda_body heq hs
  have HMbody : PiInertFrameMinimum D Ω out (proofEraseCtx (blocks.actual (B.inst x') :: Λ))
      (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
        (((pre'.map (·.subst (VExpr.Subst.one x').lift)).map (proofErase (B.inst x' :: Γ))).map
          blocks.underBinder.erased)) smaller (frames+1) := by
    simpa only [proofEraseCtx, EB, EI] using HMbody
  have WI := EqSpecializationFrame.inst W.agree.left hA HX.hasType.2
    (HX.subst henv.orderedStrong W.agree.left hΔ)
  have hBi : env.HasType univs Γ (B.inst x') (.sort z) := by
    simpa only [VExpr.inst_eq, VExpr.subst] using hB.subst henv.orderedStrong WI.actual WI.target.wf
  have hyi : env.HasType univs Δ y ((B.inst x').subst σ) := by
    simpa only [VExpr.inst_eq] using (WI.term hΔ hB).defeq hy
  have WH := W.under_binder hΔ hBi hyi
  have JH := J.under_binder W hBi
  refine ⟨x', pre'.map (·.subst (VExpr.Subst.one x').lift), smaller,
    HX, HP, hpi, hni, EI, HMbody, ?_, hsmall, by omega⟩
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, v'', w'', _, pending, [], _,
    HP, WH, JH, hpi, hni, .inl rfl, ?_⟩
  simpa only [List.append_nil] using HMbody.forget

end Lean4Lean.VEnv.Strengthening
