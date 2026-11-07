import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstructorFieldAncestry
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstructorProjectionContinuation

/-! # The selected body root retains the projection observer

The field-ancestry cut need not fix the final major in its remaining minimum.
Its actual application frame and final projection give a smaller minimum at
the selected root spine, allowing competing body endpoints and majors.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- The selected root and its actual typed projection continuation, minimal
against all competing paths from the root spine. The bound is the enclosing
projected computation's count. No guarded substitution transport is asserted. -/
def PiInertObservedBodyRoot (D : Definitions) (Ω : List ProofShape)
    (family : Name) (index : Nat) (out : ProofShape) (bound : Nat)
    (stage : Nat) (Δ : List ProofShape) (source target : ProofShape) : Prop :=
  ∃ pending tailCost endpoint continuationCost K,
    1+tailCost+continuationCost < bound ∧ TypedSource Δ (ProofShape.mkApps source pending) ∧
    PiInertStage D stage Δ source target ∧
    ScopedComputeCount (PiInertStage D stage) tailCost Δ (ProofShape.mkApps target pending) endpoint ∧
    PiInertProjectionContinuationRun D Ω family index out Δ K endpoint continuationCost ∧
    ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Δ
      (ProofShape.mkApps source pending) endpoint' → K endpoint' k →
      1+tailCost+continuationCost ≤ j+k

/-- Forget only the distinguished first root, retaining its smaller typed
projection minimum. The actual continuation still ends at the same observer. -/
theorem PiInertObservedBodyRoot.minimum
    (H : PiInertObservedBodyRoot D Ω family index out bound stage Δ source target) :
    ∃ pending smaller, smaller < bound ∧
      PiInertProjectionContinuationMinimum D Ω family index out Δ
        (ProofShape.mkApps source pending) smaller := by
  obtain ⟨pending, tailCost, endpoint, continuationCost, K, hsmall, HT, HR, RT, HK, HM⟩ := H
  refine ⟨pending, 1+tailCost+continuationCost, hsmall, K, stage, 1+tailCost,
    continuationCost, endpoint, HT, ?_, HK, rfl, HM⟩
  simpa only [Nat.add_zero] using
    ((ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := pending))).trans RT

/-- A selected nested function eta descends again while retaining the final
projection and decreasing the same count. This uses its actual suffix and
continuation, not a fresh unrelated minimum at the same source. -/
theorem PiInertObservedBodyRoot.eta_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (RN : ScopedTypeRecovery Guard Δ source (.forallE A B)) (SD : DomainSort Δ A u)
    (H : PiInertObservedBodyRoot D Ω family index out bound stage Δ source
      (.lam A (.app (source.liftN 1) (etaArgument u)))) :
    ∃ smaller, smaller < bound ∧
      PiInertProjectionContinuationMinimum D Ω family index out (A :: Δ)
        (.app (source.liftN 1) (etaArgument u)) smaller := by
  obtain ⟨pending, tailCost, endpoint, continuationCost, K, hsmall, HT, HR, RT, HK, HM⟩ := H
  obtain ⟨smaller, hless, Hminimum⟩ := pi_inert_eta_projection_continuation_frames
    heq hs hguard HT RN SD (ScopedComputeCount.beta BetaRed.refl) HR RT HK
    (cost := 1+tailCost+continuationCost) (by omega) HM
  exact ⟨smaller, by omega, Hminimum⟩

/-- A native structure root has no pending applications in the observed
minimum, by actual typing. Thus its smaller minimum starts at the full source. -/
theorem PiInertObservedBodyRoot.structure_minimum
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HE : NativeMaskedStructureExpansion Guard Δ source target)
    (H : PiInertObservedBodyRoot D Ω family index out bound stage Δ source target) :
    ∃ smaller, smaller < bound ∧
      PiInertProjectionContinuationMinimum D Ω family index out Δ source smaller := by
  obtain ⟨pending, smaller, hsmall, K, n, cb, ck, endpoint, HT, RB, HK, hcost, HM⟩ := H.minimum
  have E := TypedSource.structure_eta_pending_nil hguard HT HE
  subst pending
  exact ⟨smaller, hsmall, K, n, cb, ck, endpoint, HT, RB, HK, hcost, HM⟩

/-- Attach the final projection minimum to the already selected body root.
The actual root, prefix, component budgets and suffixes remain unchanged.
Competing remaining paths may change their body endpoint, major and stages;
only the final projected output is fixed. -/
theorem CountedEtaBodySpineCut.projected_root
    {Root : Nat → List ProofShape → ProofShape → ProofShape → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps (ProofShape.mkApps (.const c ls) pre) args))
    (HTproj : TypedSource Δ (.proj family index original))
    (RN : ScopedTypeRecovery Guard Δ (ProofShape.mkApps (.const c ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (RPrefix : ScopedComputeCount (PiInertStage D n) cp Δ original
      (ProofShape.mkApps (ProofShape.mkApps (.const c ls) pre) args))
    (REta : PiInertStage D n Δ (ProofShape.mkApps (.const c ls) pre)
      (.lam A (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u))))
    (H : CountedEtaBodySpineCut D n Δ c ls pre A u args major ct Root)
    (RObserve : ScopedComputeCount (PiInertStage D observerStage) observerCost Δ
      (.proj family index major) out)
    (hcost : cp+1+ct+observerCost ≤ cost)
    (hmin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ
      (.proj family index original) out → cost ≤ j) :
    CountedEtaBodySpineCut D n Δ c ls pre A u args major ct
      (fun m Ξ source target => Root m Ξ source target ∧
        PiInertObservedBodyRoot D Δ family index out cost m Ξ source target) := by
  obtain ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hb, RF, RX, RS, RD, HL, HA, RP, HR, HN, RT, HM, HMC, HI, HTR, WI, HC, HG⟩ := H
  have RRoot : ScopedComputeCount (PiInertStage D m) (1+tb) (A :: Δ)
      (ProofShape.mkApps (ProofShape.mkApps (.const c ls') bodyPre) bodyPending) body' := by
    simpa only [Nat.add_zero] using
      ((ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := bodyPending))).trans RT
  have RB := RP.trans (by simpa only [ProofShape.mkApps_append] using RRoot)
  obtain ⟨HTbody, _⟩ := pi_inert_eta_body_interpretation heq hs hguard HT RN SD RX
  have HTwhole : TypedSource (A :: Δ)
      (ProofShape.mkApps (ProofShape.mkApps (.const c ls') bodyPre) bodyPending) := by
    simpa only [ProofShape.mkApps_append] using HTbody.pi_inert_compute heq hs RP.forget
  have HTend := HTwhole.pi_inert_compute heq hs RRoot.forget
  have HTlong := HT.pi_inert_compute heq hs
    (((ScopedComputeCount.base REta).mkApps (ScopedArgumentsCount.refl (args := args))).forget)
  have Rbeta : ScopedComputeCount (PiInertStage D n) 0 Δ
      (ProofShape.mkApps (.lam A' body') (x' :: xs'))
      (ProofShape.mkApps (body'.inst x') xs') := by
    simpa only [ProofShape.mkApps] using
      (ScopedComputeCount.beta (BetaRed.beta (A := A') (b := body') (a := x'))).mkApps
        (ScopedArgumentsCount.refl (args := xs'))
  have HTnext := HTlong.pi_inert_compute heq hs (((RF.mkApps RX).trans Rbeta).forget)
  have HTmajor := HTnext.pi_inert_compute heq hs RS.forget
  have RWhole := pi_inert_counted_lambda_body_replace RPrefix REta RD RB RX RS
  have HTobserver := HTproj.pi_inert_compute heq hs RWhole.proj.forget
  have HK : PiInertProjectionContinuationRun D Δ family index out (A :: Δ)
      (PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs'
        (PiInertProjectionContinuation D Δ family index out)) body' (cs+observerCost) := by
    have RS' : ScopedComputeCount (PiInertStage D n) cs Δ
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') major := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS
    have HTnext' : TypedSource Δ
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext
    exact .application HTend (.inst WI) HTnext' RS'
      (.projection HTmajor HTobserver RObserve)
  refine ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hb, RF, RX, RS, RD, HL, HA, RP, HR, HN, RT, HM, HMC, HI, HTR, WI, HC, HG,
    bodyPending, tb, body', cs+observerCost, _, by omega, HTwhole, HR, RT, HK, ?_⟩
  rintro later j endpoint k RJ ⟨suffixStage, suffixCost, endpoint', tailCost, hsum, RK, tailStage, RL⟩
  have RBody : ScopedComputeCount (PiInertStage D (max m later)) (pb+j) (A :: Δ)
      (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u)) endpoint :=
    (RP.mono (pi_inert_stage_mono (Nat.le_max_left m later))).trans
      (by simpa only [ProofShape.mkApps_append] using RJ.mono (pi_inert_stage_mono (Nat.le_max_right m later)))
  have raise : ∀ {Ξ a b}, PiInertStage D n Ξ a b → PiInertStage D (max n suffixStage) Ξ a b :=
    pi_inert_stage_mono (Nat.le_max_left n suffixStage)
  have RK' : ScopedComputeCount (PiInertStage D (max n suffixStage)) suffixCost Δ
      (ProofShape.mkApps (endpoint.inst x') xs') endpoint' := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      RK.mono (pi_inert_stage_mono (Nat.le_max_right n suffixStage))
  have RAlt := pi_inert_counted_lambda_body_replace (RPrefix.mono raise) (raise REta)
    (RD.mono raise) RBody (RX.mono raise) RK'
  have RFinal := (RAlt.mono (pi_inert_stage_mono (Nat.le_max_left _ tailStage))).proj.trans
    (RL.mono (pi_inert_stage_mono (Nat.le_max_right _ tailStage)))
  have HH := hmin _ _ RFinal
  omega

/-- The combined root invariant supports the next recursive step. Function
eta yields another smaller body minimum with the same projection observer.
Structure eta yields a smaller minimum on the full pair whose first field
has the bounded original-scope origin. Readout for these minima remains open. -/
theorem PairEtaOriginalFieldRoot.observed_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : PairEtaOriginalFieldRoot D Δ original pre u before after stage Ξ source target)
    (HO : PiInertObservedBodyRoot D Δ family index out bound stage Ξ source target) :
    (∃ A innerU smaller, smaller < bound ∧
      PiInertProjectionContinuationMinimum D Δ family index out (A :: Ξ)
        (.app (source.liftN 1) (etaArgument innerU)) smaller) ∨
    (∃ short c levels later j smaller, j < before+after ∧ TypedSource Δ short ∧
      ScopedComputeCount (PiInertStage D later) j Δ original short ∧
      source = ProofShape.mkApps (.const c levels) [short.liftN 1, etaArgument u] ∧
      smaller < bound ∧
      PiInertProjectionContinuationMinimum D Δ family index out Ξ source smaller) := by
  rcases HF with ⟨k, hk, HE⟩ | ⟨k, short, c, levels, later, j, hk, hj, HT, R, E, HE⟩
  · cases HE with
    | intro RN SD =>
      obtain ⟨smaller, hsmall, HM⟩ := HO.eta_descent heq hs
        (erased_static_structure_eta_expansion_stage_descent heq hs k) RN SD
      exact .inl ⟨_, _, smaller, hsmall, HM⟩
  · obtain ⟨smaller, hsmall, HM⟩ := HO.structure_minimum
      (erased_static_structure_eta_expansion_stage_descent heq hs k) HE
    exact .inr ⟨short, c, levels, later, j, smaller, hj, HT, R, E, hsmall, HM⟩

/-- The actual global pair cut retains both its bounded original-field
ancestry and a smaller observed execution at that very root. The bound includes
the final projection and field tail, so competing majors are permitted. -/
theorem GlobalPairFunctionEtaProjection.observed_field_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : GlobalPairFunctionEtaProjection D Γ family info source out) :
    ∃ bound, PairFunctionEtaBodyMinimum D Γ family info source out
      (fun Δ field pre u before after m Ξ source target =>
        PairEtaOriginalFieldRoot D Δ field pre u before after m Ξ source target ∧
        PiInertObservedBodyRoot D Δ family 0 out bound m Ξ source target) := by
  obtain ⟨m, field, value, major, result, stage, hm, Rreach, EM, HC,
    ⟨globalCost, RG, HG, tailCost, RField, Hfull⟩, RI, Rtail⟩ := H
  obtain ⟨cost, levels, pre, pending, target, before, after,
    RC, Hmin, HB, HL, ⟨HA, argumentCost, hargs, RArgs⟩, RP, HP, HR, RT,
    k, hk, HE, hpre, hne, hproof⟩ := HC
  cases HL
  have hcost := Hmin _ (EM ▸ RG)
  have HminAll : ∀ later j, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) major → cost ≤ j := by
    intro later j RJ
    have HH := HG later j (EM ▸ RJ)
    omega
  have hmajor : ∀ A b rest, major ≠ ProofShape.mkApps (.lam A b) rest := by
    cases RI with
    | projIota =>
      intro A b rest E
      have HH := congrArg ProofShape.constHead E
      simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HH
      cases HH
  have HT : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) := ⟨Γ, m, _, hΓ, rfl, hm, EM⟩
  have HTwhole : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName []) pre) pending) := by
    simpa only [ProofShape.mkApps_append] using HT.pi_inert_compute heq hs RP.forget
  have ht := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hm).1
  have HTproj : TypedSource (proofEraseCtx Γ)
      (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value])) := by
    have H : TypedSource (proofEraseCtx Γ) (.proj family 0 (proofErase Γ m)) :=
      ⟨Γ, .proj family 0 m, _, hΓ, rfl, ht, if_neg (not_isProof_of_sort hΓ ht)⟩
    exact EM ▸ H
  have RObserve : ScopedComputeCount (PiInertStage D stage) (1+tailCost) (proofEraseCtx Γ)
      (.proj family 0 major) out :=
    (ScopedComputeCount.base (pi_inert_stage_core (.inl (.inl (.inl RI))))).trans RField
  cases HE with
  | intro RN SD =>
    rename_i A B u
    have hguard : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D k) :=
      erased_static_structure_eta_expansion_stage_descent heq hs k
    have HBody := globally_minimal_pi_inert_eta_body_spine_cut_nonlambda heq hs
      hguard HTwhole RN SD (by simpa only [ProofShape.mkApps_append] using RP)
      HR RT HB HminAll hmajor
    have HRoot := (HBody.constructor_roots heq (henv.projectionCtorRigid hi) hD).pair_field_ancestry
      heq hs hi (by omega) hpre SD HP
    have HOriginal := HRoot.original_pair_field_budget RArgs hargs
    have HObserved := HOriginal.projected_root heq hs hguard HTwhole HTproj RN SD
      (by simpa only [ProofShape.mkApps_append] using RP) HR RObserve
      (cost := globalCost+1+tailCost) (by omega)
      (fun later j RJ => Hfull later j (EM ▸ RJ))
    exact ⟨globalCost+1+tailCost, m, field, value, major, result, stage, cost, pre, pending,
      A, B, u, k, before, after, hm, Rreach, EM, RC, HminAll, HB, hpre, hne, hproof,
      ⟨HA, argumentCost, hargs, RArgs⟩, RP, hk, RN, SD, RT, HObserved, RI, Rtail⟩

/-- The exposed pair projection either reads its original field or reaches
one cut carrying both original-field budgets and the actual smaller projection
continuation. Neither field readout through that continuation nor closure of
the resulting recursive cases is assumed here. -/
theorem proofErase_pi_inert_pair_projection_readout_or_observed_field_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (RI : Primitive D (.proj family 0 (proofErase Γ m)) field)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ m)) out) :
    (∃ later, ScopedCompute (PiInertStage D later) (proofEraseCtx Γ) field out) ∨
    ∃ bound, PairFunctionEtaBodyMinimum D Γ family info (proofErase Γ m) out
      (fun Δ field pre u before after m Ξ source target =>
        PairEtaOriginalFieldRoot D Δ field pre u before after m Ξ source target ∧
        PiInertObservedBodyRoot D Δ family 0 out bound m Ξ source target) := by
  obtain ⟨cost, RC⟩ := R.count
  rcases proofErase_pi_inert_pair_projection_global_count_readout_or_function_eta
    heq hs hi hp hf hz hadm hshape hD hΓ hm RI hout hproj RC with ⟨later, j, _, RJ⟩ | H
  · exact .inl ⟨later, RJ.forget⟩
  · exact .inr (H.observed_field_root heq hs hi hp hf hz hadm hshape hD hΓ)

end Lean4Lean.VEnv.Strengthening
