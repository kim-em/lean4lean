import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSuppliedSpineReturn

/-! # Restore supplied spines after arbitrary recognized body computation

The body path need not be component-only. Its endpoint must already be a typed
nonproof chosen spine in the original fresh scope, with the original pending
images. Producing that endpoint through recursive cuts remains a separate gap.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation

/-- An ordered insertion path is injective on erased syntax. -/
theorem EqInsertionPath.erased_injective (blocks : EqInsertionPath) :
    Function.Injective blocks.erased := by
  induction blocks with
  | nil => exact fun _ _ h => h
  | cons p blocks ih =>
    intro a b h
    exact ProofShape.liftN_inj.1 (ih h)

variable [Params]

/-- Recover typed source equality from a full native path to a recognized
nonproof endpoint. The endpoint may have a different initial type. Certificate
realization and erasure reflection align it at the original source type; no
component-path hypothesis or strengthening theorem is used. -/
theorem EqFrameInsertionChain.compute_recognized_endpoint
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (he : env.HasType univs Γ e T) (hf : env.HasType univs Γ f U)
    (hnf : ¬ IsProof Γ f)
    (R : ScopedCompute Step (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ e)) (blocks.erased (proofErase Γ f))) :
    env.IsDefEq univs Γ e f T := by
  obtain ⟨e', HE, _, EE⟩ := J.compute_certificate hstep W he R
  have E := blocks.erased_injective EE
  obtain ⟨n, HF⟩ := (proofErase_reflect W.actual.wf hf HE.hasType.2 E.symm).2 hnf
  exact HE.trans ((HF.defeq W.actual.wf).symm.of_l henv W.actual.wf HE.hasType.2)

/-- Restore a whole supplied spine after a full body computation whose endpoint
has been recognized in the original fresh source context. The supplied argument
and waiting vector are the actual computed values, with their original chosen
images. This removes the component-only restriction on the body path, but does
not produce the recognized body endpoint or its pending-image invariant. -/
theorem EqPrefixSpecializationAt.recognized_body_spine_return
    (hbody : ErasedScopedPrimitiveCertificateDescent BodyStep BodyStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ x :: rest) σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hwhole : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)))
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (HX : env.IsDefEq univs Γ x x' A) (EX : blocks.erased (proofErase Γ x') = rawX)
    (HS : EqArgumentSupplyAt Γ Δ σ (rest.map (·.subst σ)) rest')
    (Hargs : List.Forall₂ (env.IsDefEqU univs Γ) rest rest')
    (ER : ((rest'.map (proofErase Γ)).map blocks.erased) ++ rawExtra = rawRest)
    (HPbody : EqPrefixSpecializationAt (A :: Γ) Δ v w v'' w'' original pre'
      (σ.cons (x.subst σ)) (rest.map (·.subst σ) ++ pending))
    (hb' : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') G)
    (hnb' : ¬ IsProof (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre'))
    (Ebody : ((pre'.map (proofErase (A :: Γ))).map blocks.underBinder.erased) = rawBody)
    (Rbody : ScopedCompute BodyStep (proofEraseCtx (blocks.actual A :: Λ))
      (blocks.underBinder.erased (proofErase (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0]))))
      (blocks.underBinder.erased (proofErase (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre')))) :
    ∃ final : List VExpr,
      EqPrefixSpecializationAt Γ Δ v w v'' w'' original final σ pending ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest))
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) final) F ∧
      ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v'',w'']) final) ∧
      ((final.map (proofErase Γ)).map blocks.erased) ++ rawExtra =
        rawBody.map (·.inst rawX) ++ rawRest ∧
      EqPrefixSpecializationAt Γ' Δ v w v'' w'' original (final.map (·.subst ρ)) σ' pending ∧
      (((final.map (·.subst ρ)).map (proofErase Γ')).map blocks.erased) ++ rawExtra.map (·.subst υ) =
        (rawBody.map (·.inst rawX) ++ rawRest).map (·.subst υ) := by
  have WF := W.under_binder hΔ hA (HX.hasType.1.subst henv.orderedStrong W.agree.left hΔ)
  have JF := J.under_binder W hA
  have hfw : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift
      (.forallE A.lift (B.liftN 1 1)) := hf.weak henv
  have EE : VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0]) =
      .app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift (.bvar 0) := by
    simp only [VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil,
      VExpr.lift, VExpr.liftN_mkApps, VExpr.liftN]
  have hb : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B := by
    rw [EE]
    simpa only [VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
  have HEbody := JF.compute_recognized_endpoint hbody WF hb hb' hnb' Rbody
  have WI := EqSpecializationFrame.inst W.agree.left hA HX.hasType.2
    (HX.subst henv.orderedStrong W.agree.left hΔ)
  obtain ⟨HPi, _, Epi⟩ := HPbody.frame hΔ WI HEbody.hasType.2
  have HPi : EqPrefixSpecializationAt Γ Δ v w v'' w'' original (pre'.map (·.inst x')) σ
      (rest.map (·.subst σ) ++ pending) := by
    simpa only [VExpr.inst_eq, VExpr.Subst.one] using HPi
  have Epi : (pre'.map (·.inst x')).map (proofErase Γ) =
      (pre'.map (proofErase (A :: Γ))).map (·.inst (proofErase Γ x')) := by
    simpa only [VExpr.inst_eq, VExpr.Subst.one, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using Epi
  have EI : (((pre'.map (·.inst x')).map (proofErase Γ)).map blocks.erased) = rawBody.map (·.inst rawX) := by
    rw [Epi, ← Ebody, ← EX]
    simp only [List.map_map, Function.comp_def, EqInsertionPath.erased_inst]
  have HEinst : env.IsDefEqU univs Γ
      (.app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) x')
      (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.inst x'))) := by
    have HI := (HEbody.instN henv HX.hasType.2 Ctx.InstN.zero).toU
    rw [EE] at HI
    simpa only [VExpr.inst_eq, VExpr.subst_mkApps, VExpr.subst,
      VExpr.lift_subst_cons, VExpr.Subst.cons, VExpr.subst_id] using HI
  have Hhead := (IsDefEq.appDF hf HX).toU.trans henv H.1.wf HEinst
  have hsplit : env.HasType univs Γ
      (VExpr.mkApps (.app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) x) rest) F := by
    simpa only [VExpr.mkApps_append, VExpr.mkApps_cons] using hwhole
  obtain ⟨HPfinal, HEfinal, hnfinal⟩ := HPi.restore_computed_supply hΔ HS Hhead Hargs hsplit
    (by simpa only [VExpr.mkApps_append, VExpr.mkApps_cons] using hn)
  have Efinal : ((((pre'.map (·.inst x') ++ rest').map (proofErase Γ)).map blocks.erased) ++ rawExtra) =
      rawBody.map (·.inst rawX) ++ rawRest := by
    rw [List.map_append, List.map_append, EI, List.append_assoc, ER]
  obtain ⟨Hout, _, Eout⟩ := HPfinal.frame hΔ W HEfinal.hasType.2
  refine ⟨pre'.map (·.inst x') ++ rest', HPfinal, ?_, hnfinal, Efinal, Hout, ?_⟩
  · simpa only [VExpr.mkApps_append, VExpr.mkApps_cons] using HEfinal
  · rw [← Efinal, Eout]
    simp only [List.map_append, List.map_map, Function.comp_def, J.erased]


/-- Restore a recognized consumed body and read the actual suffix minimum back
to the whole chosen spine. The original source context, pending images and outer
continuation are restored, and the parent eta cost strictly decreases. Endpoint
recognition is still an input; arbitrary recursive recognition remains open. -/
theorem EqPrefixSpecializationAt.recognized_body_return_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ x :: rest) σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hwhole : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)))
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (HX : env.IsDefEq univs Γ x x' A) (EX : blocks.erased (proofErase Γ x') = rawX)
    (HS : EqArgumentSupplyAt Γ Δ σ (rest.map (·.subst σ)) rest')
    (Hargs : List.Forall₂ (env.IsDefEqU univs Γ) rest rest')
    (ER : ((rest'.map (proofErase Γ)).map blocks.erased) ++ rawExtra = rawRest)
    (Hextra : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Λ)) extra rawExtra)
    (hextra : extra = [] ∨ pending = [])
    (HPbody : EqPrefixSpecializationAt (A :: Γ) Δ v w v'' w'' original pre'
      (σ.cons (x.subst σ)) (rest.map (·.subst σ) ++ pending))
    (hb' : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') G)
    (hnb' : ¬ IsProof (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre'))
    (Ebody : ((pre'.map (proofErase (A :: Γ))).map blocks.underBinder.erased) = rawBody)
    (RB : ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (blocks.actual A :: Λ))
      (blocks.underBinder.erased (proofErase (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0]))))
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawBody))
    (HTnext : TypedSource (proofEraseCtx Λ)
      (ProofShape.mkApps ((ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawBody).inst rawX) rawRest))
    (RS : ScopedComputeCount (PiInertStage D n) cs (proofEraseCtx Λ)
      (ProofShape.mkApps ((ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawBody).inst rawX) rawRest) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ) K endpoint ck)
    (hsmall : cb+(cs+ck) < cost)
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j
      (proofEraseCtx (blocks.actual A :: Λ)) (blocks.underBinder.erased (proofErase (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])))) body →
      PiInertApplicationContinuation D (proofEraseCtx Λ) (ProofShape.Subst.one rawX) rawRest K body k →
      cb+(cs+ck) ≤ j+k) :
    ∃ final : List VExpr,
      EqPrefixSpecializationAt Γ Δ v w v'' w'' original final σ pending ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest))
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) final) F ∧
      ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v'',w'']) final) ∧
      ((final.map (proofErase Γ)).map blocks.erased) ++ rawExtra = rawBody.map (·.inst rawX) ++ rawRest ∧
      PiInertTypedContinuationMinimum D Ω out (proofEraseCtx Λ)
        (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
          (((final.map (proofErase Γ)).map blocks.erased) ++ rawExtra)) (cs+ck) ∧
      EqChainContinuationMinimum D Δ v w original Ω out (cs+ck) ∧ cs+ck < cost := by
  have Rbody : ScopedCompute (PiInertStage D m) (proofEraseCtx (blocks.actual A :: Λ))
      (blocks.underBinder.erased (proofErase (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0]))))
      (blocks.underBinder.erased (proofErase (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre'))) := by
    rw [proofErase_const_spine HPbody.1.wf hb' hnb', EqInsertionPath.erased_const_spine, Ebody]
    exact RB.forget
  obtain ⟨final, HP, HE, hnfinal, Efinal, _, _⟩ :=
    H.recognized_body_spine_return (pi_inert_stage_certificate_descent heq hs m)
      hΔ W J hwhole hn hA hf HX EX HS Hargs ER
      HPbody hb' hnb' Ebody Rbody
  have Ewhole : ProofShape.mkApps ((ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawBody).inst rawX) rawRest =
      ProofShape.mkApps (.const ``Eq.rec [v'',w''])
        (((final.map (proofErase Γ)).map blocks.erased) ++ rawExtra) := by
    rw [Efinal]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      ProofShape.subst_mkApps, ProofShape.subst, ProofShape.mkApps_append]
  have HMnext : PiInertTypedContinuationMinimum D Ω out (proofEraseCtx Λ)
      (ProofShape.mkApps ((ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawBody).inst rawX) rawRest) (cs+ck) := by
    refine ⟨K, n, cs, ck, endpoint, HTnext, RS, HK, rfl, ?_⟩
    intro later j tail k RJ HL
    have HB := HM m cb _ (j+k) RB ⟨later, j, tail, k, rfl, ?_, HL⟩
    · omega
    · simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RJ
  have HMnext := Ewhole ▸ HMnext
  have hextra' : rawExtra = [] ∨ pending = [] := by
    rcases hextra with rfl | hp
    · cases Hextra; exact .inl rfl
    · exact .inr hp
  refine ⟨final, HP, HE, hnfinal, Efinal, HMnext, ?_, by omega⟩
  exact ⟨Γ, Γ', Λ, Λ', σ, σ', ρ, τ, κ, υ, blocks, v'', w'', final, pending, rawExtra, F,
    HP, W, J, HE.hasType.2, hnfinal, hextra', HMnext⟩


end Lean4Lean.VEnv.Strengthening
