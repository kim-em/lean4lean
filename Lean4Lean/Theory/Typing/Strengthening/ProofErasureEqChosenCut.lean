import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPairedEta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqEmbeddedMinimum

/-! # Actual Eq cuts retaining the chosen target substitution

Reify the whole component vector before selecting the root prefix. The chosen
substitution and pending target vector survive this selection; the omitted
actual arguments supply its new pending vector. A paired frame can therefore
remain linked to the selected root. Ambient embeddings and saturated prefixes
still require separate treatment in the global descent.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_const_levels_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
open private tracked_spine_hole
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTargetPrefixMinimum
variable [Params]

/-- Reify actual component paths while preserving the particular assignment,
including head-level changes. Target level well-formedness comes from the
actual reached spine, not an extra requirement on the chosen substitution. -/
theorem EqPrefixSpecializationAt.compute_levels
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HL : List.Forall₂ (· ≈ ·) [v',w'] ls)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Γ))
      (pre.map (proofErase Γ)) raw)
    (HT : TypedSource (proofEraseCtx Γ) (ProofShape.mkApps (.const ``Eq.rec ls) raw)) :
    ∃ v'' w'' pre', ls = [v'',w''] ∧
      EqPrefixSpecializationAt Γ Δ v w v'' w'' original pre' σ pending ∧
      pre'.map (proofErase Γ) = raw ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F := by
  obtain ⟨v'', w'', rfl⟩ : ∃ v'' w'', ls = [v'',w''] := by
    cases HL with | cons _ HL => cases HL with | cons _ HL => cases HL; exact ⟨_, _, rfl⟩
  have HW := typed_const_levels_wf
    (show TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ))) from
      ⟨Γ, _, F, H.1.wf, rfl, hf, proofErase_const_spine H.1.wf hf hn⟩)
  have HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']) :=
    ⟨_, .constDF heq.2.2.1 HW (typed_const_levels_wf HT) (by rfl) HL⟩
  obtain ⟨pre', HP, EP, HE⟩ := H.compute
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
    H.1.wf H.1.wf (Ctx.LiftN.zero []) hΔ hf HC
    (by simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id] using HA)
  exact ⟨v'', w'', pre', rfl, HP, by
    simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id] using EP, HE⟩

/-- A counted non-level root with its actual source terms, the same chosen
substitution and the same external pending target vector. The whole supplied
spine is retained, so selecting its prefix does not lose actual supply ancestry.
This predicate covers a direct semantic realization in the current scope;
iterated ambient embeddings are not hidden in its witnesses. -/
def ChosenEqSpineCut (D : Definitions) (Γ Δ : List VExpr) (v w : VLevel)
    (original : List VExpr) (σ : VExpr.Subst) (pending : List VExpr)
    (n : Nat) (source endpoint : ProofShape) (budget : Nat) : Prop :=
  ∃ v' w' pre rest F target cp ct,
    EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ rest) σ pending ∧
    env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ rest)) F ∧
    ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ rest)) ∧
    cp+1+ct ≤ budget ∧
    ScopedComputeCount (PiInertStage D n) cp (proofEraseCtx Γ) source
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre ++ rest).map (proofErase Γ))) ∧
    PiInertStage D n (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ))) target ∧
    ¬ LevelPrimitive univs
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ))) target ∧
    ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Γ)
      (ProofShape.mkApps target (rest.map (proofErase Γ))) endpoint

/-- Extract the actual first non-level cut without forgetting the chosen
assignment. Every raw component has a typed semantic realization in the same
scope. Both branches keep that assignment and the external pending vector;
no compatibility with a replacement existential witness is needed. -/
theorem EqPrefixSpecializationAt.chosen_counted_spine_or_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (R : ScopedComputeCount (PiInertStage D n) cost (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ))) endpoint) :
    (∃ v'' w'' pre', endpoint = ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (proofErase Γ)) ∧
      EqPrefixSpecializationAt Γ Δ v w v'' w'' original pre' σ pending ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F) ∨
    ChosenEqSpineCut D Γ Δ v w original σ pending n
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ))) endpoint cost := by
  have HTsource : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ))) :=
    ⟨Γ, _, F, H.1.wf, rfl, hf, proofErase_const_spine H.1.wf hf hn⟩
  rcases R.const_spine_or_cut (Good := fun _ => LevelPrimitive univs)
      (@level_primitive_spine_roots univs ``Eq.rec) with
    ⟨ls, args, EO, HL, HA⟩ | ⟨ls, rawPre, rawRest, target, cp, ct, hc, HL, HA, RP, HR, HN, RT⟩
  · have HT := EO ▸ HTsource.pi_inert_compute heq hs R.forget
    obtain ⟨v'', w'', pre', rfl, HP, EP, HE⟩ := H.compute_levels heq hs hΔ hf hn HL HA HT
    exact .inl ⟨v'', w'', pre', by simpa only [EP] using EO, HP, HE⟩
  · have HT := HTsource.pi_inert_compute heq hs RP.forget
    obtain ⟨v'', w'', full, rfl, HP, EP, HE⟩ := H.compute_levels heq hs hΔ hf hn HL HA HT
    have Epre : (full.take rawPre.length).map (proofErase Γ) = rawPre := by
      rw [List.map_take, EP, List.take_left]
    have Erest : (full.drop rawPre.length).map (proofErase Γ) = rawRest := by
      rw [List.map_drop, EP, List.drop_left]
    refine .inr ⟨v'', w'', full.take rawPre.length, full.drop rawPre.length, F, target, cp, ct,
      ?_, ?_, ?_, hc, ?_, ?_, ?_, ?_⟩
    · simpa only [List.take_append_drop] using HP
    · simpa only [List.take_append_drop] using HE.hasType.2
    · simpa only [List.take_append_drop] using
        (fun hp => hn ((isProof_congr H.1.wf HE).2 hp))
    · simpa only [List.map_append, Epre, Erest] using RP
    · simpa only [Epre] using HR
    · simpa only [Epre] using HN
    · simpa only [Erest] using RT

/-- A selected short-prefix cut in an actual all-stage minimum either reads
the target equation or descends strictly beneath native eta while retaining
both the chosen target assignment and its paired actual frame. The recovered
raw annotation is realized in the current semantic scope, so the new minimum
and the new frame refer to the same binder. A pending target image is required;
saturated prefixes and ambient embeddings remain outside this statement. -/
theorem EqPrefixSpecializationAt.paired_hole_cut_eq_or_smaller
    {C : ScopedHole Ξ (proofEraseCtx Γ)}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' [α,a,M,minor,b] pre σ (y :: rest))
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
    env.IsDefEq univs Δ a b α ∨ ∃ A B u,
      env.HasType univs Γ A (.sort u) ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B) ∧
      target = .lam (proofErase Γ A)
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          ((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ)))) ∧
      ct+ck < cost ∧
      PiInertTypedContinuationMinimum D Ω out (proofEraseCtx (A :: Γ))
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          ((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ)))) (ct+ck) ∧
      EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' [α,a,M,minor,b]
        (pre.map VExpr.lift ++ [VExpr.bvar 0]) (σ.cons y) rest ∧
      EqSpecializationFrame (A :: Γ) (A.subst ρ :: Γ') Δ
        (σ.cons y) (σ'.cons y) ρ.lift τ.lift ∧
      env.HasType univs (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B ∧
      ¬ IsProof (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) := by
  rcases (H.embedding hf hn).hole_cut_eq_or_smaller heq hs hreg hoff hRec hΔ ht
      HC HT RP HR HN RT HK HE HO hcost hmin with
    Hlower | ⟨k, rawA, rawB, u, Etarget, _, RN, SD, hsmall, HM, _⟩
  · exact .inl Hlower
  · have Ee := proofErase_const_spine H.1.wf hf hn
    obtain ⟨A, B, hfPi, EA, _⟩ := proofErase_scoped_recovered_pi_descend
      (erased_static_structure_eta_expansion_stage_descent heq hs k)
      H.1.wf H.1.wf (Ctx.LiftN.zero []) hf
      (by simpa only [List.length_nil, ProofShape.liftN_zero, Ee] using RN)
    have EA : proofErase Γ A = rawA := by
      simpa only [List.length_nil, ProofShape.liftN_zero] using EA
    obtain ⟨_, hPi⟩ := hfPi.isType henv H.1.wf
    obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
    have SD' : DomainSort (proofEraseCtx Γ) ((proofErase Γ A).liftN 0) u := by
      simpa only [ProofShape.liftN_zero, EA] using SD
    have hA := SD'.descend H.1.wf H.1.wf (Ctx.LiftN.zero []) hA
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨H.1.wf, u, hA⟩
    obtain ⟨Hfresh, Wfresh, _, _, _⟩ := H.eta_frame hΔ W ht hA hfPi
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
    rw [← Ebody, Ee] at EB
    have hnb : ¬ IsProof (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) := by
      intro hp
      rw [proofErase_eq_proof.2 hp] at EB
      cases EB
    rw [proofErase_const_spine hΓA hb hnb] at EB
    refine .inr ⟨A, B, u, hA, hfPi, ?_, hsmall, ?_, Hfresh, Wfresh, hb, hnb⟩
    · simpa only [EA, EB] using Etarget
    · simpa only [proofEraseCtx, EA, EB] using HM

/-- The result of descending one actual native eta cut with its old frame
still linked. The new current scope and the frame's outgoing scope contain
the same dependent binder, interpreted by the old actual substitution. This
is a strictly smaller actual continuation minimum, not merely a completion. -/
def PairedEqBodyMinimum (D : Definitions) (Γ Γ' Δ : List VExpr) (v w : VLevel)
    (original : List VExpr) (σ σ' ρ : VExpr.Subst) (τ : ProofShape.Subst)
    (Ω : List ProofShape) (out : ProofShape) (budget : Nat) : Prop :=
  ∃ A u y pending v' w' pre F smaller,
    env.HasType univs Γ A (.sort u) ∧ smaller < budget ∧
    PiInertTypedContinuationMinimum D Ω out (proofEraseCtx (A :: Γ))
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase (A :: Γ)))) smaller ∧
    EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original pre (σ.cons y) pending ∧
    EqSpecializationFrame (A :: Γ) (A.subst ρ :: Γ') Δ
      (σ.cons y) (σ'.cons y) ρ.lift τ.lift ∧
    env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F ∧
    ¬ IsProof (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)

/-- Apply paired strict descent to the actual cut extracted from a chosen
spine history. Prefix selection moves the actual omitted arguments into the
pending target vector using the same substitution. If no target argument
remains, the selected source has exactly five arguments; that saturated cut
is returned with its actual prefix and suffix paths. Resolving that branch,
ambient embeddings, and later continuation consumption is still necessary
for a global strengthening proof. -/
theorem ChosenEqSpineCut.eq_or_paired_smaller_or_saturated
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
    ∃ v' w' pre F target cp ct,
      pre.length = 5 ∧
      EqPrefixSpecializationAt Γ Δ v w v' w' [α,a,M,minor,b] pre σ [] ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F ∧
      ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) ∧
      cp+1+ct ≤ budget ∧
      ScopedComputeCount (PiInertStage D n) cp (proofEraseCtx Γ) source
        (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ))) ∧
      PiInertStage D n (proofEraseCtx Γ)
        (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ))) target ∧
      ¬ LevelPrimitive univs
        (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ))) target ∧
      ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Γ) target endpoint := by
  obtain ⟨v', w', pre, rest, F, target, cp, ct, HP, hf, hn, hc, RP, HR, HN, RT⟩ := H
  have Hprefix : EqPrefixSpecializationAt Γ Δ v w v' w' [α,a,M,minor,b] pre σ
      (rest.map (·.subst σ) ++ pending) := by
    simpa only [List.take_left, List.drop_left] using HP.take pre.length
  have hsplit : env.HasType univs Γ
      (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) rest) F := by
    simpa only [VExpr.mkApps_append] using hf
  obtain ⟨Fp, hfp⟩ := VExpr.WF.of_mkApps henv HP.1.wf ⟨_, hsplit⟩
  have hnp : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) :=
    nonproof_spine_head HP.1.wf hsplit
      (by simpa only [VExpr.mkApps_append] using hn)
  cases Epending : rest.map (·.subst σ) ++ pending with
  | nil =>
    have Enil : rest = [] ∧ pending = [] := by
      have EL := congrArg List.length Epending
      simp only [List.length_append, List.length_map, List.length_nil] at EL
      exact ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega)⟩
    obtain ⟨rfl, rfl⟩ := Enil
    have Hprefix : EqPrefixSpecializationAt Γ Δ v w v' w' [α,a,M,minor,b] pre σ [] := by
      simpa only [List.map_nil, List.nil_append] using Hprefix
    have hlen := Hprefix.2.2.length_eq
    have hlen : pre.length = 5 := by
      simpa only [List.length_cons, List.length_nil, List.length_append, List.length_map,
        Nat.add_zero, Nat.reduceAdd] using hlen.symm
    exact .inr (.inr ⟨v', w', pre, Fp, target, cp, ct, hlen, Hprefix, hfp, hnp, hc,
      by simpa only [List.append_nil] using RP, HR, HN,
      by simpa only [List.map_nil, ProofShape.mkApps] using RT⟩)
  | cons y tail =>
    have Hprefix : EqPrefixSpecializationAt Γ Δ v w v' w' [α,a,M,minor,b] pre σ (y :: tail) :=
      Epending ▸ Hprefix
    obtain ⟨C, HC, EC⟩ := tracked_spine_hole (proofEraseCtx Γ) (rest.map (proofErase Γ))
    have RPC : ScopedComputeCount (PiInertStage D n) cp (proofEraseCtx Γ) source
        (C.plug (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ)))) := by
      rw [EC]
      simpa only [List.map_append, ProofShape.mkApps_append] using RP
    have RTC : ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Γ) (C.plug target) endpoint := by
      rw [EC]
      exact RT
    rcases Hprefix.paired_hole_cut_eq_or_smaller heq hs hreg hoff hRec hΔ ht W hfp hnp
        HC HT RPC HR HN RTC HK HE HO (cost := cost) (by omega) hmin with
      Hlower | ⟨A, B, u, hA, _, _, hsmall, HM, Hfresh, Wfresh, hb, hnb⟩
    · exact .inl Hlower
    · exact .inr (.inl ⟨A, u, y, tail, v', w', pre.map VExpr.lift ++ [VExpr.bvar 0], B,
        ct+ck, hA, hsmall, HM, Hfresh, Wfresh, hb, hnb⟩)

end Lean4Lean.VEnv.Strengthening
