import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqChainArgumentHistory

/-! # Joint chosen-prefix and supplied-continuation eta descent

The recovered lower domain, fresh chosen binder and actual supplied history
must belong to the same eta step. Start with the whole actual supplied Eq
spine, derive its omitted argument's typing, and retain both records together.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
open private tracked_spine_hole
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTargetPrefixMinimum
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Restore the computed waiting arguments to the current chosen prefix.
Target-image agreement restores the pending vector, while their independently
retained source equalities restore whole-application typing. The two relations
have different roles; target-image agreement alone is not used to infer source
typing. The head equality must still be derived from its actual body path. -/
theorem EqPrefixSpecializationAt.restore_computed_supply
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ (chosen ++ pending))
    (HS : EqArgumentSupplyAt Γ Δ σ chosen actual)
    (Hhead : env.IsDefEqU univs Γ f (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (Hargs : List.Forall₂ (env.IsDefEqU univs Γ) previous actual)
    (ht : env.HasType univs Γ (VExpr.mkApps f previous) T)
    (hn : ¬ IsProof Γ (VExpr.mkApps f previous)) :
    EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ actual) σ pending ∧
      env.IsDefEq univs Γ (VExpr.mkApps f previous)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ actual)) T ∧
      ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ actual)) := by
  have HE : env.IsDefEq univs Γ (VExpr.mkApps f previous)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ actual)) T := by
    simpa only [VExpr.mkApps_append] using
      (IsDefEqU.mkApps_args H.1.wf Hhead Hargs ht).of_l henv H.1.wf ht
  exact ⟨H.append_pending_agree hΔ HS.2, HE, fun hp => hn ((isProof_congr H.1.wf HE).2 hp)⟩

/-- A native eta cut with an actual omitted lower argument constructs its
fresh chosen prefix and its supplied continuation history from the same
recovered domain. The first chosen image is derived from that omitted argument;
no later consumption agreement is an input. Upper extra arguments remain
untracked. The resulting smaller minimum retains the fresh paired chain.
The case with no local supplied argument still needs the enclosing history. -/
theorem EqPrefixSpecializationAt.supplied_eta_chain_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveCertificateDescent Guard Guard)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ x :: rest) σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hwhole : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)))
    (HT : TypedSource (proofEraseCtx Λ) source)
    (RN : ScopedTypeRecovery Guard (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)))
      (.forallE rawA rawB))
    (SD : DomainSort (proofEraseCtx Λ) rawA u)
    (RP : ScopedComputeCount (PiInertStage D n) cp (proofEraseCtx Λ) source
      (ProofShape.mkApps (blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)))
        ((((x :: rest).map (proofErase Γ)).map blocks.erased) ++ extra)))
    (HR : PiInertStage D n (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)))
      (.lam rawA (.app
        ((blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))).liftN 1)
        (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Λ)
      (ProofShape.mkApps (.lam rawA (.app
        ((blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))).liftN 1)
        (etaArgument u))) ((((x :: rest).map (proofErase Γ)).map blocks.erased) ++ extra)) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ) K endpoint ck)
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j
      (proofEraseCtx Λ) source tail → K tail k → cost ≤ j+k) :
    ∃ A B,
      env.HasType univs Γ A (.sort u) ∧ env.HasType univs Γ x A ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B) ∧
      proofErase Λ (blocks.actual A) = rawA ∧
      EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original
        (pre.map VExpr.lift ++ [VExpr.bvar 0]) (σ.cons (x.subst σ))
        (rest.map (·.subst σ) ++ pending) ∧
      EqSpecializationFrame (A :: Γ) (A.subst ρ :: Γ') Δ
        (σ.cons (x.subst σ)) (σ'.cons (x.subst σ)) ρ.lift τ.lift ∧
      EqFrameInsertionChain (A :: Γ) (A.subst ρ :: Γ') ρ.lift τ.lift
        (blocks.actual A :: Λ) (blocks.actual (A.subst ρ) :: Λ')
        κ.lift υ.lift blocks.underBinder ∧
      env.HasType univs (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B ∧
      ¬ IsProof (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) ∧
      EqSuppliedEtaContinuation D n Γ Δ Λ σ blocks A x (x.subst σ) (rest.map (·.subst σ)) rest
        (blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))) u
        Ω out endpoint ck cost extra K ∧
      ∃ smaller, smaller < cost ∧
        PiInertTypedContinuationMinimum D Ω out (proofEraseCtx (blocks.actual A :: Λ))
          (blocks.underBinder.erased (proofErase (A :: Γ)
            (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])))) smaller ∧
        EqChainContinuationMinimum D Δ v w original Ω out smaller := by
  have Hprefix : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ
      (x.subst σ :: (rest.map (·.subst σ) ++ pending)) := by
    simpa only [List.take_left, List.drop_left, List.map_cons, List.cons_append] using H.take pre.length
  have hsplit : env.HasType univs Γ
      (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (x :: rest)) F := by
    simpa only [VExpr.mkApps_append] using hwhole
  obtain ⟨Fp, hfp⟩ := VExpr.WF.of_mkApps henv H.1.wf ⟨_, hsplit⟩
  have hnp := nonproof_spine_head H.1.wf hsplit (by simpa only [VExpr.mkApps_append] using hn)
  obtain ⟨A, B, hA, hfPi, Ectx, Hfresh, Wfresh, Jfresh, hb, hnb, EB⟩ :=
    Hprefix.eta_insertion_chain hguard hΔ W J ht hfp hnp RN SD
  have EA : proofErase Λ (blocks.actual A) = rawA := (List.cons.inj Ectx).1
  obtain ⟨_, _, HX, _, _⟩ := H.eta_supply_frame hguard.descent hΔ ht hwhole hA hfPi
    (ScopedCompute.refl (Step := Guard) (e := proofErase Γ x))
  have hx := HX.hasType.1
  have HS : EqArgumentSupplyAt Γ Δ σ (x.subst σ :: rest.map (·.subst σ)) (x :: rest) := by
    apply EqArgumentSupplyAt.of_typed hΔ H.1
    intro e he
    exact (mkApps_arguments_wf henv H.1.wf ⟨_, hwhole⟩).2 e (List.mem_append_right pre he)
  have HH := pi_inert_eta_chain_argument_history heq hs hguard.descent hΔ HS W J hA hx
    (HT.pi_inert_compute heq hs RP.forget) (by simpa only [EA] using RN) RP
    (by simpa only [EA] using HR) (by simpa only [EA] using RT) HK hcost HM
  obtain ⟨smaller, hsmall, HMbody⟩ := HH.minimum
  have HMbody : PiInertTypedContinuationMinimum D Ω out (proofEraseCtx (blocks.actual A :: Λ))
      (blocks.underBinder.erased (proofErase (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])))) smaller := by
    simpa only [EB] using HMbody
  refine ⟨A, B, hA, hx, hfPi, EA, Hfresh, Wfresh, Jfresh, hb, hnb, HH, smaller, hsmall, HMbody, ?_⟩
  refine ⟨A :: Γ, A.subst ρ :: Γ', blocks.actual A :: Λ, blocks.actual (A.subst ρ) :: Λ',
    σ.cons (x.subst σ), σ'.cons (x.subst σ), ρ.lift, τ.lift, κ.lift, υ.lift, blocks.underBinder,
    v', w', pre.map VExpr.lift ++ [VExpr.bvar 0], rest.map (·.subst σ) ++ pending, [], B,
    Hfresh, Wfresh, Jfresh, hb, hnb, .inl rfl, ?_⟩
  simpa only [List.append_nil, proofErase_const_spine Hfresh.1.wf hb hnb,
    EqInsertionPath.erased_const_spine] using HMbody

/-- Classify an actual non-level Eq-prefix cut whose suffix begins with a
tracked lower argument. Positive guards yield the original equation; otherwise
the actual eta step simultaneously constructs its fresh chosen prefix and
supplied continuation history. The selected extra arguments and original
continuation are retained. Empty local supply still requires older history,
and subsequent component-only continuation steps remain outside this theorem. -/
theorem EqPrefixSpecializationAt.supplied_chain_cut_eq_or_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' [α,a,M,minor,b] (pre ++ x :: rest) σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hwhole : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)))
    (HT : TypedSource (proofEraseCtx Λ) source)
    (RP : ScopedComputeCount (PiInertStage D n) cp (proofEraseCtx Λ) source
      (ProofShape.mkApps
        (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map blocks.erased))
        ((((x :: rest).map (proofErase Γ)).map blocks.erased) ++ extra)))
    (HR : PiInertStage D n (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map blocks.erased)) target)
    (HN : ¬ LevelPrimitive univs
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map blocks.erased)) target)
    (RT : ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Λ)
      (ProofShape.mkApps target ((((x :: rest).map (proofErase Γ)).map blocks.erased) ++ extra)) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ) K endpoint ck)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU))
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j
      (proofEraseCtx Λ) source tail → K tail k → cost ≤ j+k) :
    env.IsDefEq univs Δ a b α ∨ ∃ A B u,
      env.HasType univs Γ A (.sort u) ∧ env.HasType univs Γ x A ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B) ∧
      target = .lam (proofErase Λ (blocks.actual A)) (.app
        ((blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))).liftN 1)
        (etaArgument u)) ∧
      EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' [α,a,M,minor,b]
        (pre.map VExpr.lift ++ [VExpr.bvar 0]) (σ.cons (x.subst σ))
        (rest.map (·.subst σ) ++ pending) ∧
      EqSpecializationFrame (A :: Γ) (A.subst ρ :: Γ') Δ
        (σ.cons (x.subst σ)) (σ'.cons (x.subst σ)) ρ.lift τ.lift ∧
      EqFrameInsertionChain (A :: Γ) (A.subst ρ :: Γ') ρ.lift τ.lift
        (blocks.actual A :: Λ) (blocks.actual (A.subst ρ) :: Λ')
        κ.lift υ.lift blocks.underBinder ∧
      env.HasType univs (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B ∧
      ¬ IsProof (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) ∧
      EqSuppliedEtaContinuation D n Γ Δ Λ σ blocks A x (x.subst σ) (rest.map (·.subst σ)) rest
        (blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))) u
        Ω out endpoint ck cost extra K ∧
      ∃ smaller, smaller < cost ∧
        PiInertTypedContinuationMinimum D Ω out (proofEraseCtx (blocks.actual A :: Λ))
          (blocks.underBinder.erased (proofErase (A :: Γ)
            (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])))) smaller ∧
        EqChainContinuationMinimum D Δ v w [α,a,M,minor,b] Ω out smaller := by
  have Hprefix : EqPrefixSpecializationAt Γ Δ v w v' w' [α,a,M,minor,b] pre σ
      (x.subst σ :: (rest.map (·.subst σ) ++ pending)) := by
    simpa only [List.take_left, List.drop_left, List.map_cons, List.cons_append] using H.take pre.length
  have hsplit : env.HasType univs Γ
      (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (x :: rest)) F := by
    simpa only [VExpr.mkApps_append] using hwhole
  obtain ⟨Fp, hfp⟩ := VExpr.WF.of_mkApps henv H.1.wf ⟨_, hsplit⟩
  have hnp := nonproof_spine_head H.1.wf hsplit (by simpa only [VExpr.mkApps_append] using hn)
  have Eraw : blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)) =
      ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map blocks.erased) := by
    rw [proofErase_const_spine H.1.wf hfp hnp, EqInsertionPath.erased_const_spine]
  have HP := (Hprefix.chain_prefix_completion W J hfp hnp).embedding
  obtain ⟨C, HC, EC⟩ := tracked_spine_hole (proofEraseCtx Λ)
    ((((x :: rest).map (proofErase Γ)).map blocks.erased) ++ extra)
  have RPC : ScopedComputeCount (PiInertStage D n) cp (proofEraseCtx Λ) source
      (C.plug (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map blocks.erased))) := by
    rw [EC]; exact RP
  have RTC : ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Λ) (C.plug target) endpoint := by
    rw [EC]; exact RT
  rcases HP.hole_cut_eq_or_smaller heq hs hreg hoff hRec hΔ ht HC HT RPC HR HN RTC HK HE HO hcost HM with
    Hlower | ⟨k, rawA, rawB, u, rfl, _, RN, SD, _, _, _⟩
  · exact .inl Hlower
  · obtain ⟨A, B, hA, hx, hfPi, EA, Hfresh, Wfresh, Jfresh, hb, hnb, HH, smaller, hsmall, HMbody, HMchain⟩ :=
      H.supplied_eta_chain_descent heq hs
        (erased_static_structure_eta_expansion_stage_certificate_descent heq hs k) hΔ W J ht
        hwhole hn HT (by simpa only [Eraw] using RN) SD (by simpa only [Eraw] using RP)
        (by simpa only [Eraw] using HR) (by simpa only [Eraw] using RT) HK hcost HM
    exact .inr ⟨A, B, u, hA, hx, hfPi, by simp only [EA, Eraw], Hfresh, Wfresh, Jfresh, hb, hnb, HH,
      smaller, hsmall, HMbody, HMchain⟩

end Lean4Lean.VEnv.Strengthening
