import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqChosenSupplyDescent

/-! # Return an actually consumed eta body to its whole supplied spine

Body components descend before the actual supplied argument is instantiated.
The body's source equality gives the consumed head equality; the waiting
arguments' source equalities then restore the original whole application type.
Their chosen images independently restore its original pending vector.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_const_levels_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton
variable [Params]

/-- Consume the actual argument recorded by the eta history after component
computation of its body, then restore the entire computed waiting supply.
Both source equality and chosen-image agreement are derived or retained in
their original scopes. The old paired frame and insertion chain remain valid,
and the resulting raw spine includes every untracked upper extra argument.
Non-level body cuts require their own descent, not this component readout. -/
theorem EqPrefixSpecializationAt.supplied_chain_spine_return
    (hbody : ErasedScopedPrimitiveCertificateDescent BodyStep BodyStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ x :: rest) σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hwhole : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)))
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (HX : env.IsDefEq univs Γ x x' A) (EX : blocks.erased (proofErase Γ x') = rawX)
    (HS : EqArgumentSupplyAt Γ Δ σ (rest.map (·.subst σ)) rest')
    (Hargs : List.Forall₂ (env.IsDefEqU univs Γ) rest rest')
    (ER : ((rest'.map (proofErase Γ)).map blocks.erased) ++ rawExtra = rawRest)
    (HC : env.IsDefEqU univs (A :: Γ) (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx (blocks.actual A :: Λ)))
      (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased) rawBody) :
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
  have HP : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ
      (x.subst σ :: (rest.map (·.subst σ) ++ pending)) := by
    simpa only [List.take_left, List.drop_left, List.map_cons, List.cons_append] using H.take pre.length
  have Hfresh := HP.eta hΔ ht hA hf
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
  obtain ⟨pre', HPbody, _, _, Ebody, _, HEbody⟩ :=
    Hfresh.compute_insertion_chain hbody hΔ WF JF hb HC HA
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

/-- Continue along the actual post-consumption suffix after restoring the
whole chosen spine. The original context, assignment, paired frame and chain
are recovered, with the old pending vector and all computed upper extras.
Minimality comes from the recorded body/application predicate and the actual
body path; the returned minimum uses the unchanged outer continuation. Its
cost is strictly below the parent eta budget even if body computation costs
zero. The body-component premises still require classification of that path. -/
theorem EqPrefixSpecializationAt.supplied_chain_return_minimum
    (hbody : ErasedScopedPrimitiveCertificateDescent BodyStep BodyStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ x :: rest) σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
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
    (HC : env.IsDefEqU univs (A :: Γ) (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx (blocks.actual A :: Λ)))
      (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased) rawBody)
    (RB : ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (blocks.actual A :: Λ)) source
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawBody))
    (HTnext : TypedSource (proofEraseCtx Λ)
      (ProofShape.mkApps ((ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawBody).inst rawX) rawRest))
    (RS : ScopedComputeCount (PiInertStage D n) cs (proofEraseCtx Λ)
      (ProofShape.mkApps ((ProofShape.mkApps (.const ``Eq.rec [v'',w'']) rawBody).inst rawX) rawRest) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ) K endpoint ck)
    (hsmall : cb+(cs+ck) < cost)
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j
      (proofEraseCtx (blocks.actual A :: Λ)) source body →
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
  obtain ⟨final, HP, HE, hnfinal, Efinal, _, _⟩ :=
    H.supplied_chain_spine_return hbody hΔ W J ht hwhole hn hA hf HX EX HS Hargs ER HC HA
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

/-- Read the actual consumed body's counted path. A component-only path
returns to the original chosen assignment and whole supplied spine at a
strictly smaller minimum. Otherwise retain its actual non-level cut under
the fresh chosen binder. Thus component computation is classified here,
not assumed; recursion through the returned nested cut still must retain
the enclosing supplied history. -/
theorem EqPrefixSpecializationAt.supplied_body_return_or_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ x :: rest) σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hwhole : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)))
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (hb : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B)
    (hnb : ¬ IsProof (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])))
    (HX : env.IsDefEq univs Γ x x' A) (EX : blocks.erased (proofErase Γ x') = rawX)
    (HS : EqArgumentSupplyAt Γ Δ σ (rest.map (·.subst σ)) rest')
    (Hargs : List.Forall₂ (env.IsDefEqU univs Γ) rest rest')
    (ER : ((rest'.map (proofErase Γ)).map blocks.erased) ++ rawExtra = rawRest)
    (Hextra : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Λ)) extra rawExtra)
    (hextra : extra = [] ∨ pending = [])
    (HTbody : TypedSource (proofEraseCtx (blocks.actual A :: Λ))
      (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased)))
    (RB : ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (blocks.actual A :: Λ))
      (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased)) body')
    (HTnext : TypedSource (proofEraseCtx Λ) (ProofShape.mkApps (body'.inst rawX) rawRest))
    (RS : ScopedComputeCount (PiInertStage D n) cs (proofEraseCtx Λ)
      (ProofShape.mkApps (body'.inst rawX) rawRest) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ) K endpoint ck)
    (hsmall : cb+(cs+ck) < cost)
    (HM : ∀ later j body k, ScopedComputeCount (PiInertStage D later) j
      (proofEraseCtx (blocks.actual A :: Λ))
      (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased)) body →
      PiInertApplicationContinuation D (proofEraseCtx Λ) (ProofShape.Subst.one rawX) rawRest K body k →
      cb+(cs+ck) ≤ j+k) :
    (∃ v'' w'' final,
      EqPrefixSpecializationAt Γ Δ v w v'' w'' original final σ pending ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest))
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) final) F ∧
      ProofShape.mkApps (body'.inst rawX) rawRest = ProofShape.mkApps (.const ``Eq.rec [v'',w''])
        (((final.map (proofErase Γ)).map blocks.erased) ++ rawExtra) ∧
      PiInertTypedContinuationMinimum D Ω out (proofEraseCtx Λ)
        (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
          (((final.map (proofErase Γ)).map blocks.erased) ++ rawExtra)) (cs+ck) ∧
      EqChainContinuationMinimum D Δ v w original Ω out (cs+ck) ∧ cs+ck < cost) ∨
    ChosenEqChainSpineCut D (A :: Γ) Δ (blocks.actual A :: Λ) blocks.underBinder v w original
      (σ.cons (x.subst σ)) (rest.map (·.subst σ) ++ pending) m
      (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased)) body' cb := by
  have HP : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ
      (x.subst σ :: (rest.map (·.subst σ) ++ pending)) := by
    simpa only [List.take_left, List.drop_left, List.map_cons, List.cons_append] using H.take pre.length
  have Hfresh := HP.eta hΔ ht hA hf
  have WF := W.under_binder hΔ hA (HX.hasType.1.subst henv.orderedStrong W.agree.left hΔ)
  have JF := J.under_binder W hA
  rcases Hfresh.chain_counted_spine_or_cut heq hs hΔ WF JF hb hnb (extra := []) (.inl rfl)
      (by simpa only [List.append_nil] using HTbody) (by simpa only [List.append_nil] using RB) with
    ⟨v'', w'', pre', extra', EO, _, _, HL, HA, Hempty, _⟩ | Hcut
  · cases Hempty
    simp only [List.append_nil] at EO HA
    cases EO
    have HC : env.IsDefEqU univs (A :: Γ) (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']) :=
      ⟨_, .constDF heq.2.2.1 (typed_const_levels_wf HTbody)
        (typed_const_levels_wf (HTbody.pi_inert_compute heq hs RB.forget)) (by rfl) HL⟩
    obtain ⟨final, HPfinal, HE, _, Efinal, HMnext, HMchain, hnext⟩ :=
      H.supplied_chain_return_minimum (pi_inert_stage_certificate_descent heq hs m) hΔ W J ht hwhole hn
        hA hf HX EX HS Hargs ER Hextra hextra HC HA RB HTnext RS HK hsmall HM
    refine .inl ⟨v'', w'', final, HPfinal, HE, ?_, HMnext, HMchain, hnext⟩
    rw [Efinal]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      ProofShape.subst_mkApps, ProofShape.subst, ProofShape.mkApps_append]
  · exact .inr (by simpa only [List.append_nil] using Hcut)

end Lean4Lean.VEnv.Strengthening
