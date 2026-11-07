import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRetainedProjectionRelay
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionFrames

/-! # Read structure fields through surviving administrative wrappers

Tracked deletions survive raw endpoint substitution and simulate the actual
later typed field path without increasing its count. Consequently a field
endpoint may retain arbitrary administrative lambda wrappers: only the final
observed output must be non-lambda-headed. Guarded paths stay in their scopes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment

/-- A finite administrative deletion trace survives raw endpoint substitution;
this substitutes syntax, not guarded computations or recovery certificates. -/
theorem AdministrativeHeadDeletion.subst (H : AdministrativeHeadDeletion e lower)
    (τ : ProofShape.Subst) : AdministrativeHeadDeletion (e.subst τ) (lower.subst τ) := by
  induction H with
  | refl => exact .refl
  | constant H => exact .constant (H.subst τ)
  | identity H => exact .identity (H.subst τ)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

variable [Params] {D : Definitions}

/-- Simulate a finite deletion trace against a typed counted computation.
Intermediate lower sources obtain typing from the trace's actual beta path.
The final deletion trace is retained and primitive cost never increases. -/
theorem AdministrativeHeadDeletion.compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : AdministrativeHeadDeletion e lower) (HT : TypedSource Δ e)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ e out) :
    ∃ lowerOut k, k ≤ cost ∧ ScopedComputeCount (PiInertStage D n) k Δ lower lowerOut ∧
      AdministrativeHeadDeletion out lowerOut := by
  induction H generalizing cost out with
  | refl => exact ⟨_, cost, by omega, R, .refl⟩
  | constant H =>
    obtain ⟨lowerOut, k, hk, RK, HK⟩ := H.compute heq hs HT R
    exact ⟨lowerOut, k, hk, RK, .constant HK⟩
  | identity H =>
    obtain ⟨lowerOut, k, hk, RK, HK⟩ := H.compute R
    exact ⟨lowerOut, k, hk, RK, .identity HK⟩
  | trans H₁ _ ih₁ ih₂ =>
    obtain ⟨middleOut, j, hj, RJ, HJ⟩ := ih₁ HT R
    have HTmiddle := HT.pi_inert_compute heq hs
      (ScopedCompute.beta (Step := PiInertStage D n) H₁.reduce)
    obtain ⟨lowerOut, k, hk, RK, HK⟩ := ih₂ HTmiddle RJ
    exact ⟨lowerOut, k, by omega, RK, HJ.trans HK⟩

/-- At a non-lambda final output every surviving deletion has been consumed.
This transports readout from the original input to its deleted version, keeping
the exact output, ambient stage and a nonincreasing primitive budget. -/
theorem AdministrativeHeadDeletion.readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : AdministrativeHeadDeletion e lower) (HT : TypedSource Δ e)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ e out) :
    ∃ k, k ≤ cost ∧ ScopedComputeCount (PiInertStage D n) k Δ lower out := by
  obtain ⟨lowerOut, k, hk, RK, HK⟩ := H.compute heq hs HT R
  exact ⟨k, hk, HK.eq_of_nonlambda hout ▸ RK⟩

/-- A counted terminal factorization for arbitrary sorted projection endpoints.
The endpoint is exact modulo its recorded administrative deletion trace; the
computed major and zero/one terminal action stay within the original budget. -/
theorem pi_inert_sorted_projection_terminal_frames_count
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ (.proj s i m) (.sort u))
    (R : ScopedComputeCount (PiInertStage D n) cost Δ (.proj s i m) out) :
    ∃ major lower cm, AdministrativeHeadDeletion out lower ∧
      ScopedComputeCount (PiInertStage D n) cm Δ m major ∧
      ((lower = .proj s i major ∧ cm ≤ cost) ∨
       (Primitive D (.proj s i major) lower ∧ cm+1 ≤ cost)) := by
  obtain ⟨lower, HD, HF⟩ := pi_inert_sorted_projection_frames_count heq hs HT R
  rcases HF with ⟨major, cm, hcm, EO, RM⟩ | ⟨major, field, before, after, HB, RM, RI, RF⟩
  · exact ⟨major, lower, cm, HD, RM, .inl ⟨EO, hcm⟩⟩
  · cases RI with
    | projIota hi hl hg =>
      have hj := (List.getElem?_eq_some_iff.1 hg).1
      refine ⟨_, lower, before+after, HD, RM.trans (RF.selected_argument hg),
        .inr ⟨?_, by omega⟩⟩
      exact .projIota hi (by simpa only [List.length_set] using hl) (by simp [hj])

/-- Any sorted projection field endpoint, including an unconsumed lambda
wrapper, gives a smaller pair-readout failure in a global frame minimum whose
final observed output is non-lambda-headed. Only administrative endpoint
deletions and ordinary terminal selection cross the substitution. -/
theorem pi_inert_projection_frames_smaller_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (HSort : ControlTyping Ξ (.proj family 0 source) (.sort u))
    (RF : ScopedComputeCount (PiInertStage D bodyStage) fieldCost Ξ (.proj family 0 source) field)
    (HT : TypedSource Ξ (ProofShape.mkApps (.const info.ctorName []) [field, value']))
    (W : ContextSubstitution Ξ Δ τ)
    (HNext : TypedSource Δ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [field, value']).subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Δ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [field, value']).subst τ) pending) major)
    (RObserve : ScopedComputeCount (PiInertStage D observerStage) ck Δ (.proj family 0 major) out)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hgap : fieldCost+cs+ck < cost)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Ξ source endpoint →
      PiInertApplicationContinuation D Δ τ pending
        (PiInertProjectionContinuation D Δ family 0 out) endpoint k → cost ≤ j+k) :
    pending = [] ∧ cs+ck < cost ∧
      PiInertPairProjectionBudgetFailure D Δ family info
        (field.subst τ) (value'.subst τ) out (cs+ck) := by
  obtain ⟨major', lower, cm, HD, RM, HF⟩ :=
    pi_inert_sorted_projection_terminal_frames_count heq hs HSort RF
  have EP := TypedSource.closed_constructor_image_pending_nil hi hp hz (by simp [hf]) HT W HNext
  have EI : (ProofShape.mkApps (.const info.ctorName []) [field, value']).subst τ =
      ProofShape.mkApps (.const info.ctorName []) [field.subst τ, value'.subst τ] := by
    simp only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons, List.map_nil]
  rw [EP, EI] at HNext RNext
  have HTimage : TypedSource Δ
      (ProofShape.mkApps (.const info.ctorName []) [field.subst τ, value'.subst τ]) := by
    simpa only [ProofShape.mkApps] using HNext
  have RImage : ScopedComputeCount (PiInertStage D nextStage) cs Δ
      (ProofShape.mkApps (.const info.ctorName []) [field.subst τ, value'.subst τ]) major := by
    simpa only [ProofShape.mkApps] using RNext
  have HTfield : TypedSource Δ (field.subst τ) :=
    (ScopedHole.appFn (.appArg (.const info.ctorName []) .hole) (value'.subst τ)).typed HTimage
  refine ⟨EP, by omega, HTimage, ⟨max nextStage observerStage,
    (RImage.mono (pi_inert_stage_mono (Nat.le_max_left _ _))).proj.trans
      (RObserve.mono (pi_inert_stage_mono (Nat.le_max_right _ _)))⟩, ?_⟩
  intro later j hj RJ
  obtain ⟨k, hk, RK⟩ := (HD.subst τ).readout heq hs HTfield hout RJ
  rcases HF with ⟨EF, HC⟩ | ⟨RI, HC⟩
  · have HK : PiInertApplicationContinuation D Δ τ pending
        (PiInertProjectionContinuation D Δ family 0 out) major' k := by
      rw [EP]
      refine ⟨later, 0, major'.subst τ, k, by omega, .beta .refl, later, ?_⟩
      simpa only [EF, ProofShape.subst] using RK
    have HH := HM bodyStage cm major' k RM HK
    omega
  · have RIimage : Primitive D (.proj family 0 (major'.subst τ)) (lower.subst τ) := RI.subst
    have HK : PiInertApplicationContinuation D Δ τ pending
        (PiInertProjectionContinuation D Δ family 0 out) major' (1+k) := by
      rw [EP]
      exact ⟨later, 0, major'.subst τ, 1+k, by omega, .beta .refl, later,
        (ScopedComputeCount.base (pi_inert_stage_core (.inl (.inl (.inl RIimage))))).trans RK⟩
    have HH := HM bodyStage cm major' (1+k) RM HK
    omega

/-- An actual native structure root and its constructor-component tail reduce
a global frame minimum to a strictly smaller pair-readout failure, regardless
of the type field's endpoint shape. The final output must be non-lambda-headed.
Later constructor roots and further consuming binder frames remain unresolved. -/
theorem pi_inert_native_structure_components_frames_smaller_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target)
    (HC : ∃ fields, target = ProofShape.mkApps (.const info.ctorName []) fields ∧
      ScopedArgumentsCount (PiInertStage D bodyStage) (proofEraseCtx Γ) ca fields [field, value'])
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (W : ContextSubstitution (proofEraseCtx Γ) Δ τ)
    (HNext : TypedSource Δ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [field, value']).subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Δ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [field, value']).subst τ) pending) major)
    (RObserve : ScopedComputeCount (PiInertStage D observerStage) ck Δ (.proj family 0 major) out)
    (hgap : ca+cs+ck < cost)
    (HM : ∀ later j endpoint k,
      ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ) (proofErase Γ m) endpoint →
      PiInertApplicationContinuation D Δ τ pending
        (PiInertProjectionContinuation D Δ family 0 out) endpoint k → cost ≤ j+k) :
    pending = [] ∧ cs+ck < cost ∧
      PiInertPairProjectionBudgetFailure D Δ family info
        (field.subst τ) (value'.subst τ) out (cs+ck) := by
  obtain ⟨HSort, HTtarget, value, ET⟩ :=
    proofErase_native_pair_structure_field (D := D) hstep hi hp hf hz hadm hshape hΓ hm H
  obtain ⟨fields, EF, HA⟩ := HC
  have EFields := (ProofShape.const_spine_inj (EF.symm.trans ET)).2.2
  rw [EFields] at HA
  have RT : ScopedComputeCount (PiInertStage D bodyStage) ca (proofEraseCtx Γ) target
      (ProofShape.mkApps (.const info.ctorName []) [field, value']) := by
    rw [ET]
    simpa only [Nat.zero_add] using (ScopedComputeCount.beta BetaRed.refl).mkApps HA
  have HT := HTtarget.pi_inert_compute heq hs RT.forget
  cases HA with
  | cons RF rest =>
    cases rest with
    | cons RV last =>
      cases last
      exact pi_inert_projection_frames_smaller_failure heq hs hi hp hf hz HSort
        RF HT W HNext RNext RObserve hout (by omega) HM

/-- Analyze the whole actual tail after a native structure root. A component
tail yields a strictly smaller readout failure without restricting the field
endpoint. Otherwise the first non-level constructor root retains its counted
prefix and a strictly smaller typed continuation minimum at its target. This
locates the remaining root obligation rather than assuming component-only work. -/
theorem pi_inert_native_structure_tail_smaller_failure_or_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target)
    (HRoot : PiInertStage D bodyStage (proofEraseCtx Γ) (proofErase Γ m) target)
    (RBody : ScopedComputeCount (PiInertStage D bodyStage) cb (proofEraseCtx Γ) target endpoint)
    (W : PiInertEndpointMap (proofEraseCtx Γ) Δ τ)
    (HNext : TypedSource Δ (ProofShape.mkApps (endpoint.subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Δ
      (ProofShape.mkApps (endpoint.subst τ) pending) major)
    (HTObserve : TypedSource Δ (.proj family 0 major))
    (RObserve : ScopedComputeCount (PiInertStage D observerStage) ck Δ (.proj family 0 major) out)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (HM : ∀ later j endpoint' k,
      ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ) (proofErase Γ m) endpoint' →
      PiInertApplicationContinuation D Δ τ pending
        (PiInertProjectionContinuation D Δ family 0 out) endpoint' k → 1+cb+cs+ck ≤ j+k) :
    (pending = [] ∧ cs+ck < 1+cb+cs+ck ∧ ∃ field value',
      endpoint = ProofShape.mkApps (.const info.ctorName []) [field, value'] ∧
      PiInertPairProjectionBudgetFailure D Δ family info
        (field.subst τ) (value'.subst τ) out (cs+ck)) ∨
    (∃ value pre bodyPending rootTarget cp ct ca,
      target = ProofShape.mkApps (.const info.ctorName []) [.proj family 0 (proofErase Γ m), value] ∧
      cp+1+ct ≤ cb ∧ ca ≤ cp ∧
      ScopedArgumentsCount (PiInertStage D bodyStage) (proofEraseCtx Γ) ca
        [.proj family 0 (proofErase Γ m), value] (pre ++ bodyPending) ∧
      ScopedComputeCount (PiInertStage D bodyStage) cp (proofEraseCtx Γ) target
        (ProofShape.mkApps (.const info.ctorName []) (pre ++ bodyPending)) ∧
      PiInertStage D bodyStage (proofEraseCtx Γ)
        (ProofShape.mkApps (.const info.ctorName []) pre) rootTarget ∧
      ¬ LevelPrimitive univs (ProofShape.mkApps (.const info.ctorName []) pre) rootTarget ∧
      ScopedComputeCount (PiInertStage D bodyStage) ct (proofEraseCtx Γ)
        (ProofShape.mkApps rootTarget bodyPending) endpoint ∧
      ct+cs+ck < 1+cb+cs+ck ∧
      PiInertProjectionContinuationMinimum D Δ family 0 out (proofEraseCtx Γ)
        (ProofShape.mkApps rootTarget bodyPending) (ct+cs+ck)) := by
  obtain ⟨HSort, HTtarget, value, ET⟩ :=
    proofErase_native_pair_structure_field D hstep hi hp hf hz hadm hshape hΓ hm H
  have RB : ScopedComputeCount (PiInertStage D bodyStage) cb (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) [.proj family 0 (proofErase Γ m), value]) endpoint := by
    rw [← ET]
    exact RBody
  rcases RB.const_spine_components_or_cut_counted (U := univs) with
    ⟨levels, fields, ch, ca, hcounts, rfl, HL, _, HA⟩ |
    ⟨levels, pre, bodyPending, rootTarget, cp, ct, ca, hcut, hca, HL, HA, RP, HR, HN, RT⟩
  · cases HL
    cases HA with
    | cons RF rest =>
      cases rest with
      | cons RV last =>
        cases last
        obtain ⟨EP, hsmall, HF⟩ := pi_inert_projection_frames_smaller_failure heq hs hi hp hf hz
          HSort RF (HTtarget.pi_inert_compute heq hs RBody.forget) W.interpretation HNext
          RNext RObserve hout (by omega) HM
        exact .inl ⟨EP, hsmall, _, _, rfl, HF⟩
  · cases HL
    have RP' : ScopedComputeCount (PiInertStage D bodyStage) cp (proofEraseCtx Γ) target
        (ProofShape.mkApps (.const info.ctorName []) (pre ++ bodyPending)) := by
      rw [ET]
      exact RP
    have RPrefixRoot : ScopedComputeCount (PiInertStage D bodyStage) (1+cp+1) (proofEraseCtx Γ)
        (proofErase Γ m) (ProofShape.mkApps rootTarget bodyPending) := by
      have RR := (ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := bodyPending))
      rw [← ProofShape.mkApps_append] at RR
      simpa only [Nat.add_zero] using ((ScopedComputeCount.base HRoot).trans RP').trans RR
    have HToriginal : TypedSource (proofEraseCtx Γ) (proofErase Γ m) := ⟨Γ, m, _, hΓ, rfl, hm, rfl⟩
    have HK : PiInertProjectionContinuationRun D Δ family 0 out (proofEraseCtx Γ)
        (PiInertApplicationContinuation D Δ τ pending (PiInertProjectionContinuation D Δ family 0 out))
        endpoint (cs+ck) :=
      .application (HTtarget.pi_inert_compute heq hs RBody.forget) W HNext RNext
        (.projection (HNext.pi_inert_compute heq hs RNext.forget) HTObserve RObserve)
    refine .inr ⟨value, pre, bodyPending, rootTarget, cp, ct, ca, ET, hcut, hca, HA, RP', HR, HN, RT,
      by omega, _, bodyStage, ct, cs+ck, endpoint,
      HToriginal.pi_inert_compute heq hs RPrefixRoot.forget, RT, HK, by omega, ?_⟩
    intro later j endpoint' k RJ RK
    have RAlt := (RPrefixRoot.mono (pi_inert_stage_mono (Nat.le_max_left bodyStage later))).trans
      (RJ.mono (pi_inert_stage_mono (Nat.le_max_right bodyStage later)))
    have HH := HM _ _ endpoint' k RAlt RK
    omega

end Lean4Lean.VEnv.Strengthening
