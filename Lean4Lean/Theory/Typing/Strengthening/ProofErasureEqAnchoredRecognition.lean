import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqAnchoredConsumedState

/-! # Complete recognition of anchored Eq histories

Index the exact global recognition statement by primitive cost and incoming
depth. Existing chosen and unused lambdas reduce to strictly smaller calls in
that lexicographic order. Fresh eta cuts initialize depth-one states at strictly
smaller primitive cost. Together these prove the full recognizer and close the
lifted Eq-probe exposure theorem. General semantic coverage remains separate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private tracked_spine_hole
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTargetPrefixMinimum
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
variable [Params]

/-- The original recognition obligation at a fixed primitive cost and incoming
depth. All contexts, endpoints, finite stages, target Eq data and unrestricted
continuation minima remain generalized, so recursive calls can change scope. -/
def EqAnchoredRecognitionAt (D : Definitions) (cost depth : Nat) : Prop :=
  ∀ {Δ Γ₀ Λ₀ : List VExpr} {σ₀ : VExpr.Subst} {blocks₀ : EqInsertionPath}
    {pending₀ : List VExpr} {v w : VLevel} {α a M minor b T : VExpr}
    {source endpoint out : ProofShape} {Ω : List ProofShape} {outU : VLevel}
    {K : ProofShape → Nat → Prop} {n ck : Nat},
    env.HasCanonicalEq → D.Sound env univs →
    (∃ data, recursorData ``Eq.rec = some data ∧ data.majorOffset = 5) →
    (∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs) →
    OnCtx Δ (env.IsType univs) →
    env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T →
    EqSpecializationFrame Γ₀ Γ₀ Δ σ₀ σ₀ VExpr.Subst.id ProofShape.Subst.id →
    EqFrameInsertionChain Γ₀ Γ₀ VExpr.Subst.id ProofShape.Subst.id
      Λ₀ Λ₀ VExpr.Subst.id ProofShape.Subst.id blocks₀ →
    EqAnchoredEndpoint D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ v w [α,a,M,minor,b] source depth →
    TypedSource (proofEraseCtx Λ₀) source →
    ScopedComputeCount (PiInertStage D n) cost (proofEraseCtx Λ₀) source endpoint →
    PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ₀) K endpoint ck →
    CarrierExposure out → ControlTyping Ω out (.sort outU) →
    (∀ later j tail k, ScopedComputeCount (PiInertStage D later) j
      (proofEraseCtx Λ₀) source tail → K tail k → cost+ck ≤ j+k) →
    env.IsDefEq univs Δ a b α ∨ ∃ returnedDepth, returnedDepth ≤ depth+cost ∧
      EqAnchoredEndpoint D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ v w [α,a,M,minor,b] endpoint returnedDepth

/-- Existing anchored lambdas are closed under recognition from strictly smaller
cost/depth calls. Actual body minima retain their original scopes; consumed
suffix minima retain the exact returned state. Both chosen and unused frames
preserve the target Eq alternative and the required output-depth bound. -/
theorem EqAnchoredRecognitionAt.positive
    (hd : 0 < depth)
    (IH : ∀ smaller inner, (smaller < cost ∨ smaller = cost ∧ inner < depth) →
      EqAnchoredRecognitionAt D smaller inner) :
    EqAnchoredRecognitionAt D cost depth := by
  intro Δ Γ Λ σ blocks pending v w α a M minor b T source endpoint out Ω outU K n ck
    heq hs hreg hRec hΔ ht W J H HT R HK HE HO HM
  rcases H.outermost W J hd with
    ⟨A, u, y, args, remaining, body, inner, hA, hy, HA, HB, rfl, rfl⟩ |
    ⟨A, u, args, body, inner, rfl, hA, HB, rfl, rfl⟩
  · have WB : EqSpecializationFrame (A :: Γ) (A :: Γ) Δ (σ.cons y) (σ.cons y)
        VExpr.Subst.id ProofShape.Subst.id := by
      simpa only [VExpr.subst_id, VExpr.id_lift, ProofShape.Subst.id_lift] using W.under_binder hΔ hA hy
    have JB : EqFrameInsertionChain (A :: Γ) (A :: Γ) VExpr.Subst.id ProofShape.Subst.id
        (blocks.actual A :: Λ) (blocks.actual A :: Λ) VExpr.Subst.id ProofShape.Subst.id
        blocks.underBinder := by
      simpa only [VExpr.subst_id, VExpr.id_lift, ProofShape.Subst.id_lift] using J.under_binder W hA
    have Ectx : proofEraseCtx (blocks.actual A :: Λ) =
        blocks.erased (proofErase Γ A) :: proofEraseCtx Λ := by
      rw [proofEraseCtx, J.erase_actual W hA]
    obtain ⟨HTbody, HC⟩ := pi_inert_lambda_recognition_readout heq hs HT R HK HM
    rw [← Ectx] at HTbody HC
    rcases HC with
      ⟨A', body', args', u', cd, cb, ca, m, SD, hcost, rfl, RD, RB, RX, HKbody, HMbody⟩ |
      ⟨A', body', x', xs', u', cd, cb, ca, cs, m, SD, hcost, RD, RB, RX, WX, HTnext, RS, HKbody, HMbody, HMsuffix⟩
    · rcases IH cb inner (by omega) heq hs hreg hRec hΔ ht WB JB HB HTbody RB HKbody HE HO HMbody with
        HEq | ⟨returned, hbound, Hbody⟩
      · exact .inl HEq
      · exact .inr (HA.retained_recognition heq hs hΔ W J hA hy RD RB RX Hbody hbound (by omega))
    · rcases IH cb inner (by omega) heq hs hreg hRec hΔ ht WB JB HB HTbody RB HKbody HE HO HMbody with
        HEq | ⟨returned, hbound, Hbody⟩
      · exact .inl HEq
      · obtain ⟨Hstart, _, hsmall⟩ := HA.consumed_recognition
          (cd := cd) (cs := cs) (cost := cost) heq hs hΔ W J hA RB RX Hbody hbound (by omega)
        rcases IH cs returned hsmall heq hs hreg hRec hΔ ht W J Hstart HTnext RS HK HE HO HMsuffix with
          HEq | ⟨resultDepth, hresult, Hresult⟩
        · exact .inl HEq
        · exact .inr ⟨resultDepth, by omega, Hresult⟩
  · have JB : EqFrameInsertionChain Γ Γ VExpr.Subst.id ProofShape.Subst.id
        (A :: Λ) (A :: Λ) VExpr.Subst.id ProofShape.Subst.id (blocks ++ [(1,0)]) := by
      simpa only [VExpr.subst_id, VExpr.id_lift, ProofShape.Subst.id_lift] using J.insert_domain W hA
    have Ectx : proofEraseCtx (A :: Λ) = proofErase Λ A :: proofEraseCtx Λ := rfl
    obtain ⟨HTbody, HC⟩ := pi_inert_lambda_recognition_readout heq hs HT R HK HM
    rw [← Ectx] at HTbody HC
    rcases HC with
      ⟨A', body', args', u', cd, cb, ca, m, SD, hcost, rfl, RD, RB, RX, HKbody, HMbody⟩ |
      ⟨A', body', x', xs', u', cd, cb, ca, cs, m, SD, hcost, RD, RB, RX, WX, HTnext, RS, HKbody, HMbody, HMsuffix⟩
    · rcases IH cb inner (by omega) heq hs hreg hRec hΔ ht W JB HB HTbody RB HKbody HE HO HMbody with
        HEq | ⟨returned, hbound, Hbody⟩
      · exact .inl HEq
      · exact .inr ⟨returned+1, by omega, Hbody.retain_unused heq hs hΔ W J hA RD⟩
    · rcases IH cb inner (by omega) heq hs hreg hRec hΔ ht W JB HB HTbody RB HKbody HE HO HMbody with
        HEq | ⟨returned, hbound, Hbody⟩
      · exact .inl HEq
      · have Hstart := Hbody.consume_unused heq hs hΔ W J hA WX xs'
        rcases IH cs returned (by omega) heq hs hreg hRec hΔ ht W J Hstart HTnext RS HK HE HO HMsuffix with
          HEq | ⟨resultDepth, hresult, Hresult⟩
        · exact .inl HEq
        · exact .inr ⟨resultDepth, by omega, Hresult⟩

/-- A fresh chosen eta creates a recognized state of depth one immediately,
before its suffix runs. Its actual waiting supply and source application typing
initialize the source anchor. This allows the entire suffix to use a strictly
smaller primitive-cost induction call, regardless of its later binder behavior. -/
theorem EqPrefixSpecializationAt.chosen_eta_anchored
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveCertificateDescent Guard Guard)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ (y :: rest))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HS : EqArgumentSupplyAt Γ Δ σ supplied actual)
    (EP : supplied ++ pending = y :: rest) (hextra : extra = [] ∨ pending = [])
    (happ : env.HasType univs Γ (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) actual) Fall)
    (hnall : ¬ IsProof Γ (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) actual))
    (RN : ScopedTypeRecovery Guard (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))) (.forallE rawA rawB))
    (SD : DomainSort (proofEraseCtx Λ) rawA u) :
    EqAnchoredEndpoint D Δ Γ Λ σ blocks pending v w original
      (ProofShape.mkApps (.lam rawA (.app
        ((blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))).liftN 1)
        (etaArgument u))) (((actual.map (proofErase Γ)).map blocks.erased) ++ extra)) 1 := by
  obtain ⟨A, B, hA, hfPi, Ectx, Hfresh, _, _, hb, hnb, EB⟩ :=
    H.eta_insertion_chain hguard hΔ W J ht hf hn RN SD
  have hy : env.HasType univs Δ y (A.subst σ) := by
    have HS := Hfresh.1
    cases HS with
    | cons _ _ hy => exact hy.hasType.1
  have EA : blocks.erased (proofErase Γ A) = rawA := by
    have E := (List.cons.inj Ectx).1
    simpa only [J.erase_actual W hA] using E
  have Ebody : VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0]) =
      .app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift (.bvar 0) := by
    simp only [VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil,
      VExpr.lift, VExpr.liftN_mkApps, VExpr.liftN]
  have HA := EqRetainedSourceAnchor.of_eta (D := D) (n := 0) (Λ := Λ) H.1.wf hfPi happ hnall HS EP hextra rfl
    (ScopedCompute.refl (e := blocks.underBinder.erased (proofErase (A :: Γ)
      (.app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift (.bvar 0)))))
  have HB : EqAnchoredEndpoint D Δ (A :: Γ) (blocks.actual A :: Λ) (σ.cons y)
      blocks.underBinder rest v w original
      (blocks.underBinder.erased (proofErase (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])))) 0 := by
    simpa only [proofErase_const_spine Hfresh.1.wf hb hnb, EqInsertionPath.erased_const_spine,
      List.append_nil] using
      (EqAnchoredEndpoint.of_spine (D := D) (Λ := blocks.actual A :: Λ)
        (blocks := blocks.underBinder) Hfresh hb hnb (extra := []) (.inl rfl))
  have HA' : EqRetainedSourceAnchor D Γ Λ Δ σ blocks A y pending rest
      (blocks.underBinder.erased (proofErase (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0]))))
      (((actual.map (proofErase Γ)).map blocks.erased) ++ extra) := by
    simpa only [Ebody] using HA
  have RD : ScopedComputeCount (PiInertStage D 0) 0 (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ A)) rawA := EA ▸ .beta .refl
  simpa only [EB] using HB.retain_chosen heq hs hΔ W J hA hy RD HA'

/-- A saturated fresh eta creates an unused upper frame at depth one. Its
actual recovered domain supplies the upper insertion, while the lower chosen
prefix and assignment stay fixed and all remaining arguments are raw extras. -/
theorem EqPrefixSpecializationAt.saturated_eta_anchored
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ [])
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HT : TypedSource (proofEraseCtx Λ) (ProofShape.mkApps (.const ``Eq.rec [v',w'])
      (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))
      (.forallE rawA rawB))
    (SD : DomainSort (proofEraseCtx Λ) rawA u) (tail : List ProofShape) :
    EqAnchoredEndpoint D Δ Γ Λ σ blocks [] v w original
      (ProofShape.mkApps (.lam rawA (.app
        ((ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)).liftN 1) (etaArgument u))) tail) 1 := by
  obtain ⟨A, hA, EA, _, _⟩ := H.saturated_chain_eta heq hs hΔ W J ht hf hn HT RN SD
  have HB := EqAnchoredEndpoint.of_spine (D := D) (Λ := A :: Λ) (blocks := blocks ++ [(1,0)])
    H hf hn (extra := extra.map (·.liftN 1) ++ [etaArgument u]) (.inr rfl)
  have RD : ScopedComputeCount (PiInertStage D 0) 0 (proofEraseCtx Λ) (proofErase Λ A) rawA := EA ▸ .beta .refl
  have HR := HB.retain_unused (args := tail) heq hs hΔ W J hA RD
  simpa only [ProofShape.liftN_mkApps, ProofShape.liftN, ProofShape.mkApps_append,
    ProofShape.mkApps, List.map_append, List.map_map, Function.comp_def,
    EqInsertionPath.erased_snoc] using HR

/-- The first non-level Eq cut either reads the original target equality or
reaches an exact recognized depth-one eta state. Keep the actual prefix and
whole suffix, so suffix recognition spends one less primitive without changing
its endpoint or continuation. -/
theorem ChosenEqChainSpineCut.eq_or_anchored_step
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : ChosenEqChainSpineCut D Γ Δ Λ blocks v w [α,a,M,minor,b] σ pending n source endpoint budget)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (HT : TypedSource (proofEraseCtx Λ) source)
    (HK : PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ) K endpoint ck)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU))
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j
      (proofEraseCtx Λ) source tail → K tail k → budget+ck ≤ j+k) :
    env.IsDefEq univs Δ a b α ∨ ∃ cp ct middle, cp+1+ct ≤ budget ∧
      ScopedComputeCount (PiInertStage D n) (cp+1) (proofEraseCtx Λ) source middle ∧
      ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Λ) middle endpoint ∧
      EqAnchoredEndpoint D Δ Γ Λ σ blocks pending v w [α,a,M,minor,b] middle 1 := by
  obtain ⟨v', w', pre, extra, arity, F, target, cp, ct, HP, hf, hn, hextra, hk, hc, RP, HR, HN, RT⟩ := H
  let args := ((pre.map (proofErase Γ)).map blocks.erased) ++ extra
  obtain ⟨C, HC, EC⟩ := tracked_spine_hole (proofEraseCtx Λ) (args.drop arity)
  have RPC : ScopedComputeCount (PiInertStage D n) cp (proofEraseCtx Λ) source
      (C.plug (ProofShape.mkApps (.const ``Eq.rec [v',w']) (args.take arity))) := by
    rw [EC, ← ProofShape.mkApps_append, List.take_append_drop]
    exact RP
  have RTC : ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Λ) (C.plug target) endpoint := by
    rw [EC]
    exact RT
  have finish (HS : EqAnchoredEndpoint D Δ Γ Λ σ blocks pending v w [α,a,M,minor,b] (C.plug target) 1) :
      env.IsDefEq univs Δ a b α ∨ ∃ cp ct middle, cp+1+ct ≤ budget ∧
        ScopedComputeCount (PiInertStage D n) (cp+1) (proofEraseCtx Λ) source middle ∧
        ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Λ) middle endpoint ∧
        EqAnchoredEndpoint D Δ Γ Λ σ blocks pending v w [α,a,M,minor,b] middle 1 :=
    .inr ⟨cp, ct, C.plug target, hc, RPC.trans (HC.counted (.base HR)), RTC, HS⟩
  rcases HP.chain_root_partition hextra hk blocks with
    ⟨y, rest, _, EP, Hprefix, Etake, Edrop⟩ | ⟨hp, _, Etake, Edrop⟩
  · have hsplit : env.HasType univs Γ
        (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.take arity)) (pre.drop arity)) F := by
      rw [← VExpr.mkApps_append, List.take_append_drop]
      exact hf
    have hnsplit : ¬ IsProof Γ
        (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.take arity)) (pre.drop arity)) := by
      rw [← VExpr.mkApps_append, List.take_append_drop]
      exact hn
    obtain ⟨Fp, hfp⟩ := VExpr.WF.of_mkApps henv HP.1.wf ⟨_, hsplit⟩
    have hnp := nonproof_spine_head HP.1.wf hsplit hnsplit
    have Ee := proofErase_const_spine HP.1.wf hfp hnp
    have HPbase : EqHeadCompletion Δ v w [α,a,M,minor,b] (proofEraseCtx Γ)
        (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.take arity))) := by
      refine ⟨Γ, Γ, 0, 0, v', w', pre.take arity, Fp, HP.1.wf, HP.1.wf, Ctx.LiftN.zero [], rfl,
        hfp, hnp, Hprefix.forget, ?_⟩
      simp only [ProofShape.liftN_zero]
    have Hembed := (EqTargetPrefixCompletion.of_completion (J.completion W hfp (.base HPbase))).embedding
    rw [Ee, EqInsertionPath.erased_const_spine] at Hembed
    rcases Hembed.hole_cut_eq_or_smaller heq hs hreg hoff hRec hΔ ht HC HT
        (by simpa only [args, Etake] using RPC) (by simpa only [Etake] using HR)
        (by simpa only [Etake] using HN) RTC HK HE HO (cost := budget+ck) (by omega) HM with
      HEq | ⟨k, rawA, rawB, u, Etarget, _, RN, SD, _⟩
    · exact .inl HEq
    · have HS := (HP.pending_argument_supply hΔ hf arity).2
      have Hfresh := Hprefix.chosen_eta_anchored heq hs
        (erased_static_structure_eta_expansion_stage_certificate_descent heq hs k)
        hΔ W J ht hfp hnp HS EP hextra hsplit hnsplit
        (by simpa only [Ee, EqInsertionPath.erased_const_spine] using RN) SD
      apply finish
      simpa only [EC, Etarget, args, Edrop, Ee, EqInsertionPath.erased_const_spine] using Hfresh
  · cases hp
    have Hembed := (HP.saturated_chain_completion W J hf hn (extra.take (arity-pre.length))).embedding
    rcases Hembed.hole_cut_eq_or_smaller heq hs hreg hoff hRec hΔ ht HC HT
        (by simpa only [args, Etake] using RPC) (by simpa only [Etake] using HR)
        (by simpa only [Etake] using HN) RTC HK HE HO (cost := budget+ck) (by omega) HM with
      HEq | ⟨k, rawA, rawB, u, Etarget, _, RN, SD, _⟩
    · exact .inl HEq
    · have HTroot := C.typed (HT.pi_inert_compute heq hs RPC.forget)
      have Hfresh := HP.saturated_eta_anchored heq hs hΔ W J ht hf hn
        (by simpa only [args, Etake] using HTroot) RN SD (args.drop arity)
      apply finish
      simpa only [EC, Etarget] using Hfresh

/-- The zero-depth induction interface: recognize a chosen Eq spine using only
recognition calls of strictly smaller primitive cost. Positive-depth states at
smaller costs are available. `eq_anchored_zero_recognition_step` proves this
interface by initializing the actual fresh eta state before processing its suffix. -/
def EqAnchoredZeroRecognitionStep (D : Definitions) : Prop :=
  ∀ cost, (∀ smaller, smaller < cost → ∀ depth, EqAnchoredRecognitionAt D smaller depth) →
    EqAnchoredRecognitionAt D cost 0

/-- Zero-depth recognition is closed by actual first-cut selection. Component
computation returns depth zero; every remaining eta initializes depth one and
its whole suffix has strictly smaller primitive cost. The parent's minimum
supplies the suffix minimum across arbitrary finite stages. -/
theorem eq_anchored_zero_recognition_step : EqAnchoredZeroRecognitionStep D := by
  intro cost IH
  intro Δ Γ Λ σ blocks pending v w α a M minor b T source endpoint out Ω outU K n ck
    heq hs hreg hRec hΔ ht W J H HT R HK HE HO HM
  obtain ⟨v', w', pre, extra, F, HP, hf, hn, hextra, rfl⟩ := H.zero_depth_spine
  rcases HP.anchored_spine_or_cut heq hs hΔ W J hf hn hextra HT R with Hend | HC
  · exact .inr ⟨0, by omega, Hend⟩
  · obtain ⟨data, hreg, hoff⟩ := hreg
    rcases HC.eq_or_anchored_step heq hs hreg hoff hRec hΔ ht W J HT HK HE HO HM with
      HEq | ⟨cp, ct, middle, hcost, RP, RT, Hmiddle⟩
    · exact .inl HEq
    · have HTmiddle := HT.pi_inert_compute heq hs RP.forget
      have HMsuffix : ∀ later j tail k,
          ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Λ) middle tail →
          K tail k → ct+ck ≤ j+k := by
        intro later j tail k RJ HL
        have RR := (RP.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
          (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
        have HH := HM _ _ _ _ RR HL
        omega
      rcases IH ct (by omega) 1 heq hs ⟨data, hreg, hoff⟩ hRec hΔ ht W J Hmiddle
          HTmiddle RT HK HE HO HMsuffix with HEq | ⟨returned, hbound, Hend⟩
      · exact .inl HEq
      · exact .inr ⟨returned, by omega, Hend⟩

/-- The proved positive-depth cases and a zero-depth step suffice for the
original global recognition obligation by nested strong induction. This is
conditional on the supplied zero-depth step; `eq_anchored_recognition` below
discharges that premise. This induction does not assert semantic path coverage. -/
theorem EqAnchoredRecognition.of_zero_step (H0 : EqAnchoredZeroRecognitionStep D) :
    EqAnchoredRecognition D := by
  have Hall : ∀ cost depth, EqAnchoredRecognitionAt D cost depth := by
    intro cost
    induction cost using Nat.strongRecOn with
    | ind cost IHcost =>
      intro depth
      induction depth using Nat.strongRecOn with
      | ind depth IHdepth =>
        by_cases hz : depth = 0
        · subst depth
          exact H0 cost IHcost
        · apply EqAnchoredRecognitionAt.positive (by omega)
          intro smaller inner hsmall
          rcases hsmall with hc | ⟨rfl, hi⟩
          · exact IHcost smaller hc inner
          · exact IHdepth inner hi
  intro Δ Γ Λ σ blocks pending v w α a M minor b T source endpoint out Ω outU K depth n cost ck
  exact Hall cost depth

/-- The full exact anchored recognizer, proved by primitive-cost and depth
induction. It has no recognition premise: component, fresh-eta, retained and
consumed cases are all supplied by checked local constructions. -/
theorem eq_anchored_recognition : EqAnchoredRecognition D :=
  EqAnchoredRecognition.of_zero_step eq_anchored_zero_recognition_step

/-- A lifted typed Eq probe exposing a carrier through any finite Pi-inert
stage reads the original lower index equality. This has no recognizer, frontier
or scope-agreement premise. Existence of such an exposure path for arbitrary
semantic equalities is a separate coverage question. -/
theorem pi_inert_lifted_eq_probe_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w α a M minor b))
    (Eargs : args = (([α,a,M,minor,b].map (proofErase Γ)).map (·.liftN count offset)) ++ [.proof])
    (HT : ControlTyping (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) (.sort u))
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out) (HE : CarrierExposure out) :
    env.IsDefEq univs Γ a b α :=
  EqAnchoredRecognition.lifted_probe eq_anchored_recognition heq hs hreg hoff hRec
    hΓ hΓ' W ht hn Eargs HT R HE

end Lean4Lean.VEnv.Strengthening
